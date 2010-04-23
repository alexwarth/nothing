#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

// TODO: add IJZ, IEQ, INEQ, ...
// TODO: make closures work

typedef unsigned char byte_t;
typedef int           value_t;

value_t nil, stack, sp, globals;

#define DEBUG 1

#define allocate(N, T) ((T *) calloc(N, sizeof(T)))

#define isInt(X)       ((X) & 1)
#define Int(X)         (((X) << 1) | 1)
#define IntValue(X)    ({ value_t _x = X; if (DEBUG) assert(isInt(_x)); _x >> 1; })

#define isOop(X)       (((X) & 1) == 0)
#define Oop(X)         ((X) << 1)
#define OopValue(X)    ({ value_t _x = X; if (DEBUG) assert(isOop(_x));     _x >> 1; })

void error(char *fmt, ...) {
  va_list args;
  va_start(args, fmt);
  fprintf(stderr, "error: ");
  vfprintf(stderr, fmt, args);
  fprintf(stderr, "\n");
  exit(1);
}

typedef struct OTEntry {
  size_t numSlots;
  union {
    value_t        *slots;
    struct OTEntry *next;
  } ptr;
} OTEntry;

size_t OTSize;
OTEntry *OT, *freeList;
byte_t *marked;

const size_t OrigOTSize = 1;

void growOT(void) {
  size_t  newOTSize    = OTSize > 0 ? OTSize * 2 : OrigOTSize;
  if (DEBUG) printf("growOT, new size is %li\n", newOTSize);
  OTEntry *newOT       = allocate(newOTSize, OTEntry);
  byte_t  *newMarked   = allocate(newOTSize, byte_t),
          *newIsGlobal = allocate(newOTSize, byte_t);
  memcpy(newOT, OT, sizeof(OTEntry) * OTSize);
  for (int i = OTSize; i < newOTSize; i++) {
    newOT[i].numSlots = -1;
    newOT[i].ptr.next = i + 1 < newOTSize ? &newOT[i + 1] : NULL;
    newIsGlobal[i]    = 0;
  }
  if (OTSize > 0) {
    free(OT);
    free(marked);
  }
  freeList = &newOT[OTSize];
  OTSize   = newOTSize;
  OT       = newOT;
  marked   = newMarked;
}

int mark(value_t oop) {
  if (!isOop(oop))
    return 0;
  int otIdx = OopValue(oop);
  if (marked[otIdx])
    return 0;
  marked[otIdx] = 1;
  size_t r = 1;
  OTEntry e = OT[otIdx];
  value_t *slot = e.ptr.slots;
  int n = e.numSlots;
  while (n--) {
    r += mark(*slot);
    slot++;
  }
  return r;
}

value_t numSlots(value_t oop) {
  assert(isOop(oop));
  return Int(OT[OopValue(oop)].numSlots);
}

value_t slotAt(value_t oop, value_t idx) {
  assert(isOop(oop));
  assert(isInt(idx));
  assert(Int(0) <= idx && idx < numSlots(oop));
  return OT[OopValue(oop)].ptr.slots[IntValue(idx)];
}

value_t slotAtPut(value_t oop, value_t idx, value_t val) {
  assert(isOop(oop));
  assert(isInt(idx));
  assert(Int(0) <= idx && idx < numSlots(oop));
  return OT[OopValue(oop)].ptr.slots[IntValue(idx)] = val;
}

size_t gc(void) {
  memset(marked, 0, OTSize);
  int numMarked = mark(globals);
  for (int i = 0; i < OTSize; i++) {
    if (marked[i])
      continue;
    free(OT[i].ptr.slots);
    OT[i].numSlots  = -1;
    OT[i].ptr.next  = freeList;
    freeList        = &OT[i];
  }
  if (DEBUG) printf("GC reclaimed %ld OTEntries\n", OTSize - numMarked);
  return OTSize - numMarked;
}

value_t mk(size_t numSlots) {
  if (freeList == NULL) {
    gc();
    if (freeList == NULL)
      growOT();
  }
  OTEntry *newGuy = freeList;
  freeList = freeList->ptr.next;
  newGuy->numSlots = numSlots;
  newGuy->ptr.slots = allocate(numSlots, value_t);
  return Oop(newGuy - OT);
}

#define mk1(a)       ({ value_t _r = mk(1); slotAtPut(_r, Int(0), a);                           _r; })
#define mk2(a, b)    ({ value_t _r = mk(2); slotAtPut(_r, Int(0), a); slotAtPut(_r, Int(1), b); _r; })
#define mk3(a, b, c) ({ value_t _r = mk(3); slotAtPut(_r, Int(0), a); slotAtPut(_r, Int(1), b); slotAtPut(_r, Int(2), c); _r; })

#define addGlobal(V) ({ globals = mk2(nil, globals); slotAtPut(globals, Int(0), V); })

void init(void) {
  OTSize = 0;
  growOT();
  globals = nil = mk(0);
  addGlobal(nil);
  addGlobal(stack = mk(10240));
  sp = Int(0);
}

void _print(value_t v, int n) {
  if (v == nil)
    printf("nil");
  else if (isInt(v))
    printf("%d", IntValue(v));
  else if (isOop(v)) {
    printf("[");
    if (n >= 5)
      printf("...");
    else
      for (int i = 0; i < IntValue(numSlots(v)); i++) {
        if (i > 0) printf(", ");
        _print(slotAt(v, Int(i)), n + 1);
      }
    printf("]");
  }
  else
    error("print doesn't know how to handle value (%d)\n", v);
}

void print(value_t v)   { _print(v, 1); }
void println(value_t v) { print(v); printf("\n"); }

void printStack(void) {
  printf("contents of stack: \n");
  int spv = IntValue(sp);
  while (spv > 0) {
    spv--;
    printf("  "); println(slotAt(stack, Int(spv)));
  }
  printf("that's it\n\n");
}

value_t ipb, ip, fp;

#define NewInstruction(Name, Arg) value_t Name(int isReal, value_t Arg) { \
                                    if (isReal && DEBUG) { printf("\n>>> "); println(Arg); }

NewInstruction(iPush, v)
  slotAtPut(stack, sp, v);
  sp = Int(IntValue(sp) + 1);
  return v;
}

NewInstruction(iPeek, _)
  assert(sp > Int(0));
  return slotAt(stack, Int(IntValue(sp) - 1));
}

NewInstruction(iPop, _)
  assert(sp > Int(0));
  sp = Int(IntValue(sp) - 1);
  value_t r = slotAt(stack, sp);
  slotAtPut(stack, sp, Int(0));
  return r;
}

NewInstruction(iAdd, _)
  value_t op2 = iPop(0, nil);
  return iPush(0, Int(IntValue(iPop(0, nil)) + IntValue(op2)));
}

NewInstruction(iSub, _)
  value_t op2 = iPop(0, nil);
  return iPush(0, Int(IntValue(iPop(0, nil)) - IntValue(op2)));
}

NewInstruction(iMul, _)
  value_t op2 = iPop(0, nil);
  return iPush(0, Int(IntValue(iPop(0, nil)) * IntValue(op2)));
}

NewInstruction(iBox, _)
  return iPush(0, mk1(iPop(0, nil)));
}

NewInstruction(iUnbox, _)
  return iPush(0, slotAt(iPop(0, nil), Int(0)));
}

NewInstruction(iLd, offset)
  if (isReal && DEBUG) { printf("\n>>> executing LD "); println(offset); }
  return iPush(0, slotAt(stack, Int(IntValue(fp) - IntValue(offset))));
}

NewInstruction(iArg, n)
  iLd(0, Int(4));
  int nArgs = IntValue(iPop(0, nil));
  return iLd(0, Int(5 + nArgs - IntValue(n)));
}

NewInstruction(iFv, n)
  iLd(0, Int(4));
  int nArgs = IntValue(iPop(0, nil));
  iLd(0, Int(IntValue(5 + nArgs)));
  iUnbox(0, nil);
  value_t closure = iPop(0, nil);
  return iPush(0, slotAt(closure, Int(IntValue(n) + 1)));
}

NewInstruction(iMkFun, nFreeVars)
  value_t closure = mk(IntValue(nFreeVars) + 1);
  for (int i = IntValue(nFreeVars); i >= 0; i--)
    slotAtPut(closure, Int(i), iPop(0, nil));
  return iPush(0, closure);
}

NewInstruction(iCall, nArgs)
  iPush(0, slotAt(stack, Int(IntValue(sp) - 1 - IntValue(nArgs))));
  iUnbox(0, nil); // get the closure out of its "box"
  iUnbox(0, nil); // get the code out of the closure (it's in the 1st slot of the closure)
  value_t code = iPop(0, nil);
  iPush(0, nArgs);
  iPush(0, ip);
  iPush(0, ipb);
  iPush(0, fp);
  fp  = sp;
  ip  = Int(-1);
  ipb = code;
  return nil;
}

NewInstruction(iRet, _)
  value_t r = iPop(0, nil);
  sp    = fp;
  fp    = iPop(0, nil);
  ipb   = iPop(0, nil);
  ip    = iPop(0, nil);
  int n = IntValue(iPop(0, nil));
  while (n-- > 0) iPop(0, nil);
  printf("the function was "); println(iPop(0, nil)); // the function
  return iPush(0, r);
}

NewInstruction(iJnz, n)
  value_t v = iPop(0, nil);
  if (IntValue(v) != 0)
    ip = Int(IntValue(ip) + IntValue(n));
  return nil;
}

NewInstruction(iHalt, _)
 printStack();
 exit(0);
}

enum                                   {IRET, ILD, IARG, IADD, ISUB, IMUL, IMKFUN, ICALL, IPUSH, IPOP, IBOX, IUNBOX,
                                        ISLOTAT, ISLOTATPUT, IJNZ, IHALT, IFV};
value_t (*jumpTable[])(int, value_t) = {iRet, iLd, iArg, iAdd, iSub, iMul, iMkFun, iCall, iPush, iPop, iBox, iUnbox,
                                        NULL,    NULL,       iJnz, iHalt, iFv};

void interp(value_t prog) {
  fp  = sp;
  ipb = prog;
  ip  = Int(0);
  while (1) {
    value_t instr = slotAt(ipb, ip), opcode = IntValue(slotAt(instr, Int(0))), op = slotAt(instr, Int(1));
    if (DEBUG) printStack();
    if (0 <= opcode && opcode < sizeof(jumpTable) / sizeof(value_t (*)(int, value_t)))
      jumpTable[opcode](1, op);
    else
      error("unrecognized instruction (opcode = %d)\n", opcode);
    ip = Int(IntValue(ip) + 1);
  }
}

#define LD(O)    mk2(Int(ILD),    Int(O))

#define PUSH(X)  mk2(Int(IPUSH),  Int(X))

#define MKFUN(N) mk2(Int(IMKFUN), Int(N))
#define CALL(N)  mk2(Int(ICALL),  Int(N))
#define RET      mk2(Int(IRET),   nil)
#define ARG(N)   mk2(Int(IARG),   Int(N))
#define LARG(N)  mk2(Int(ILARG),  Int(N))
#define FV(O)    mk2(Int(IFV),    Int(O))
#define LFV(O)   mk2(Int(ILFV),   Int(O))
#define HALT     mk2(Int(IHALT),  nil)
#define ADD      mk2(Int(IADD),   nil)
#define SUB      mk2(Int(ISUB),   nil)
#define MUL      mk2(Int(IMUL),   nil)
#define BOX      mk2(Int(IBOX),   nil)
#define UNBOX    mk2(Int(IUNBOX), nil)
#define JNZ(O)   mk2(Int(IJNZ),   Int(O))

/* Print all contents in the object table. */
void printOT() {
  for (int i = 0; i < OTSize; i++) {
    OTEntry *e = &OT[i];
    printf("%d: ", i);
    if (e->numSlots == -1) {
      int next = e->ptr.next - OT;
      printf("free -> %d\n", next >= 0 ? next : -1);
    }
    else {
      for (int n = 0; n < e->numSlots; n++) {
        value_t v = e->ptr.slots[n];
        if (isInt(v))
          printf("%d, ", IntValue(v)); /* Ints are shown as 123 */
        else
          printf("(%d), ", OopValue(v)); /* References are shown as (123) */
      }
      printf("\n");
    }
  }
}

int main(void) {
  init();

/*
  for (int i = 0; i < 100; i++) mk(1);
  iPush(0, mk2(Int(4), nil));
  for (int i = 0; i < 100; i++) mk(1);
  iPush(0, mk2(Int(3), iPop(0, nil)));
  for (int i = 0; i < 100; i++) mk(1);
  iPush(0, mk2(Int(2), iPop(0, nil)));
  for (int i = 0; i < 100; i++) mk(1);
  iPush(0, mk2(Int(1), iPop(0, nil)));
  for (int i = 0; i < 100; i++) mk(1);
  printStack();
*/

  value_t add = mk(6);
  addGlobal(add);
  slotAtPut(add,  Int(0), ARG(1));
  slotAtPut(add,  Int(1), UNBOX);
  slotAtPut(add,  Int(2), ARG(2));
  slotAtPut(add,  Int(3), UNBOX);
  slotAtPut(add,  Int(4), ADD);
  slotAtPut(add,  Int(5), RET);

  value_t prog = mk(9);
  addGlobal(prog);
  slotAtPut(prog, Int(0), mk2(Int(IPUSH), add));
  slotAtPut(prog, Int(1), BOX);
  slotAtPut(prog, Int(2), MKFUN(0));
  slotAtPut(prog, Int(3), PUSH(3));
  slotAtPut(prog, Int(4), BOX);
  slotAtPut(prog, Int(5), PUSH(4));
  slotAtPut(prog, Int(6), BOX);
  slotAtPut(prog, Int(7), CALL(2));
  slotAtPut(prog, Int(8), HALT);

  interp(prog);
  return 0;
}

