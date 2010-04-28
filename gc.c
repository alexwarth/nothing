#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

// Stack Layout:       ... local vars, etc.
//               fp -> oldFp
//                     oldIbp
//                     oldIp
//                     nArgs
//                     arg(n)
//                     arg(n - 1)
//                     arg(n - 2)
//                     ...
//                     arg(1)
//                     function, which is arg(0)

#define DEBUG 1

typedef unsigned char byte_t;
typedef int           value_t;

value_t nil, stack, sp, globals, ipb, ip, fp;

#define allocate(N, T) ((T *) calloc(N, sizeof(T)))

#define isInt(X)       ((X) & 1)
#define Int(X)         (((X) << 1) | 1)
#define IntValue(X)    ({ value_t _x = X; if (DEBUG) assert(isInt(_x)); _x >> 1; })

#define isOop(X)       (((X) & 1) == 0)
#define Oop(X)         ((X) << 1)
#define OopValue(X)    ({ value_t _x = X; if (DEBUG) assert(isOop(_x)); _x >> 1; })

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

const size_t OrigOTSize = 1;
size_t OTSize;
OTEntry *OT, *freeList;
byte_t *marked;

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
  while (n--)
    r += mark(*(slot++));
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

void addGlobal(value_t v) {
  slotAtPut(globals, Int(0), v);
  globals = mk2(Int(0), globals);
}

void init(void) {
  OTSize = 0;
  growOT();
  globals = mk2(Int(0), Int(0));
  addGlobal(nil = mk(0));
  addGlobal(stack = mk(10240));
  sp = Int(0);
}

void _print(value_t v, value_t n, value_t selIdx) {
  if      (v == nil) printf("nil");
  else if (isInt(v)) printf("%d", IntValue(v));
  else if (isOop(v)) { printf("[");
                       if (IntValue(n) >= 5) printf("...");
                       else                  for (int i = 0; i < IntValue(numSlots(v)); i++) {
                                               if (i > 0) printf(", ");
                                               if (i == IntValue(selIdx)) printf("<<<");
                                               _print(slotAt(v, Int(i)), Int(IntValue(n) + 1), -1);
                                               if (i == IntValue(selIdx)) printf(">>>");
                                             }
                       printf("]");
                     }
  else               error("print doesn't know how to handle value (%d)\n", v);
}

void print(value_t v)   { _print(v, Int(1), Int(-1)); }
void println(value_t v) { print(v); printf("\n"); }

void printState(void) {
  printf("ipb(ip="); print(ip); printf("): "); _print(ipb, Int(1), ip); printf("\n");
  printf("fp: "); println(fp);
  printf("/---------------------------------------------------------------------\\\n");
  int spv = IntValue(sp);
  while (spv-- > 0) { printf("  "); println(slotAt(stack, Int(spv))); }
  printf("\\---------------------------------------------------------------------/\n");
}

#define Instruction(Name, Arg) value_t Name(int quiet, value_t Arg) { \
                                 if (DEBUG && !quiet) { printf(">>> " #Name " "); println(Arg); }

Instruction(iPush, v)          slotAtPut(stack, sp, v);
                               sp = Int(IntValue(sp) + 1);
                               return v; }

Instruction(iPop, _)           assert(sp > Int(0));
                               sp = Int(IntValue(sp) - 1);
                               value_t r = slotAt(stack, sp);
                               slotAtPut(stack, sp, Int(0));
                               return r; }

Instruction(iEq, _)            return iPush(1, Int(IntValue(iPop(1, nil)) == IntValue(iPop(1, nil)))); }

Instruction(iAdd, _)           value_t op2 = iPop(1, nil);
                               return iPush(1, Int(IntValue(iPop(1, nil)) + IntValue(op2))); }

Instruction(iSub, _)           value_t op2 = iPop(1, nil);
                               return iPush(1, Int(IntValue(iPop(1, nil)) - IntValue(op2))); }

Instruction(iMul, _)           value_t op2 = iPop(1, nil);
                               return iPush(1, Int(IntValue(iPop(1, nil)) * IntValue(op2))); }

Instruction(iBox, _)           return iPush(1, mk1(iPop(1, nil))); }
Instruction(iUnbox, _)         return iPush(1, slotAt(iPop(1, nil), Int(0))); }

Instruction(iLd, offset)       return iPush(1, slotAt(stack, Int(IntValue(fp) - IntValue(offset)))); }

Instruction(iArg, n)           iLd(1, Int(4));
                               int nArgs = IntValue(iPop(1, nil));
                               return iLd(1, Int(5 + nArgs - IntValue(n))); }

Instruction(iFv, n)            iLd(1, Int(4));
                               int nArgs = IntValue(iPop(1, nil));
                               iLd(1, Int(5 + nArgs));
                               iUnbox(1, nil);
                               value_t closure = iPop(1, nil);
                               return iPush(1, slotAt(closure, Int(IntValue(n) + 1))); }

Instruction(iMkFun, nFreeVars) value_t closure = mk(IntValue(nFreeVars) + 1);
                               for (int i = IntValue(nFreeVars); i >= 0; i--)
                                 slotAtPut(closure, Int(i), iPop(1, nil));
                               return iPush(1, closure); }

Instruction(iCall, nArgs)      iPush(1, slotAt(stack, Int(IntValue(sp) - 1 - IntValue(nArgs))));
                               iUnbox(1, nil); // get the closure out of its "box"
                               iUnbox(1, nil); // get the code out of the closure (it's in the 1st slot of the closure)
                               value_t code = iPop(1, nil);
                               iPush(1, nArgs);
                               iPush(1, ip);
                               iPush(1, ipb);
                               iPush(1, fp);
                               fp  = sp;
                               ip  = Int(-1);
                               ipb = code;
                               return nil; }

Instruction(iRet, _)           value_t r = iPop(1, nil);
                               sp    = fp;
                               fp    = iPop(1, nil);
                               ipb   = iPop(1, nil);
                               ip    = iPop(1, nil);
                               int n = IntValue(iPop(1, nil));
                               while (n-- >= 0) iPop(1, nil); // pop nArgs and function
                               return iPush(1, r); }

Instruction(iJmp, n)           ip = Int(IntValue(ip) + IntValue(n)); return nil; }
Instruction(iJz,  n)           return IntValue(iPop(1, nil)) == 0 ? iJmp(1, n) : nil; }
Instruction(iJnz, n)           return IntValue(iPop(1, nil)) != 0 ? iJmp(1, n) : nil; }

enum
  {oRet, oLD, oArg, oFV, oAdd, oSub, oMul, oMkFun, oCall, oPush, oPop, oBox, oUnbox, oEq, oJmp, oJZ, oJNZ, oHalt};
value_t (*jumpTable[])(int, value_t) =
  {iRet, iLd, iArg, iFv, iAdd, iSub, iMul, iMkFun, iCall, iPush, iPop, iBox, iUnbox, iEq, iJmp, iJz, iJnz};

void interp(value_t prog) {
  fp  = sp;
  ipb = prog;
  ip  = Int(0);
  while (1) {
    value_t instr = slotAt(ipb, ip), opcode = IntValue(slotAt(instr, Int(0))), op = slotAt(instr, Int(1));
    if (DEBUG) { printf("\n\n\n"); printState(); printf("\n"); }
    if (opcode == oHalt)                                                                    { if (DEBUG) printf(">>> iHalt\n"); }
    else if (0 <= opcode && opcode < sizeof(jumpTable) / sizeof(value_t (*)(int, value_t))) jumpTable[opcode](0, op);
    else                                                                                    error("invalid opcode %d\n", opcode);
    ip = Int(IntValue(ip) + 1);
    if (DEBUG) { printf("\n"); printState(); printf("\n\n\n"); }
    if (opcode == oHalt)
      break;
  }
}

#define Push(X)  mk2(Int(oPush),  Int(X))
#define MkFun(N) mk2(Int(oMkFun), Int(N))
#define Call(N)  mk2(Int(oCall),  Int(N))
#define Ret      mk2(Int(oRet),   nil)
#define Arg(N)   mk2(Int(oArg),   Int(N))
#define FV(O)    mk2(Int(oFV),    Int(O))
#define Halt     mk2(Int(oHalt),  nil)
#define Eq       mk2(Int(oEq),    nil)
#define Add      mk2(Int(oAdd),   nil)
#define Sub      mk2(Int(oSub),   nil)
#define Mul      mk2(Int(oMul),   nil)
#define Box      mk2(Int(oBox),   nil)
#define Unbox    mk2(Int(oUnbox), nil)
#define Jmp(O)   mk2(Int(oJmp),   Int(O))
#define JZ(O)    mk2(Int(oJZ),    Int(O))
#define JNZ(O)   mk2(Int(oJNZ),   Int(O))

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
  iPush(1, mk2(Int(4), nil));
  for (int i = 0; i < 100; i++) mk(1);
  iPush(1, mk2(Int(3), iPop(1, nil)));
  for (int i = 0; i < 100; i++) mk(1);
  iPush(1, mk2(Int(2), iPop(1, nil)));
  for (int i = 0; i < 100; i++) mk(1);
  iPush(1, mk2(Int(1), iPop(1, nil)));
  for (int i = 0; i < 100; i++) mk(1);
  printState();
*/

 value_t l1 = mk(9);
addGlobal(l1);
slotAtPut(l1, Int(0), FV(0));
slotAtPut(l1, Int(1), Unbox);
slotAtPut(l1, Int(2), FV(1));
slotAtPut(l1, Int(3), Unbox);
slotAtPut(l1, Int(4), FV(2));
slotAtPut(l1, Int(5), Unbox);
slotAtPut(l1, Int(6), Add);
slotAtPut(l1, Int(7), Add);
slotAtPut(l1, Int(8), Ret);
value_t l2 = mk(6);
addGlobal(l2);
slotAtPut(l2, Int(0), mk2(Int(oPush), l1));
slotAtPut(l2, Int(1), FV(0));
slotAtPut(l2, Int(2), FV(1));
slotAtPut(l2, Int(3), Arg(1));
slotAtPut(l2, Int(4), MkFun(3));
slotAtPut(l2, Int(5), Ret);
value_t l3 = mk(5);
addGlobal(l3);
slotAtPut(l3, Int(0), mk2(Int(oPush), l2));
slotAtPut(l3, Int(1), FV(0));
slotAtPut(l3, Int(2), Arg(1));
slotAtPut(l3, Int(3), MkFun(2));
slotAtPut(l3, Int(4), Ret);
value_t l4 = mk(4);
addGlobal(l4);
slotAtPut(l4, Int(0), mk2(Int(oPush), l3));
slotAtPut(l4, Int(1), Arg(1));
slotAtPut(l4, Int(2), MkFun(1));
slotAtPut(l4, Int(3), Ret);
value_t prog = mk(17);
addGlobal(prog);
slotAtPut(prog, Int(0), mk2(Int(oPush), l4));
slotAtPut(prog, Int(1), MkFun(0));
slotAtPut(prog, Int(2), Box);
slotAtPut(prog, Int(3), Push(1));
slotAtPut(prog, Int(4), Box);
slotAtPut(prog, Int(5), Call(1));
slotAtPut(prog, Int(6), Box);
slotAtPut(prog, Int(7), Push(2));
slotAtPut(prog, Int(8), Box);
slotAtPut(prog, Int(9), Call(1));
slotAtPut(prog, Int(10), Box);
slotAtPut(prog, Int(11), Push(3));
slotAtPut(prog, Int(12), Box);
slotAtPut(prog, Int(13), Call(1));
slotAtPut(prog, Int(14), Box);
slotAtPut(prog, Int(15), Call(0));
slotAtPut(prog, Int(16), Halt);

  interp(prog);
  return 0;
}

