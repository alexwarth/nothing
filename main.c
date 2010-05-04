#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

// TODO: make this stuff OO (even ref-cells used for fvs and args), add receiver, make "global obj", add recv to stack frame, etc.
// TODO: make strings instances of String, made up of instances of Char
// TODO: use the same hashtable impl for method cache, interned strings dict., etc.
 
// Stack Layout:       ... local vars, etc.
//                     arg(n)                                     load/store(-nArgs)
//                     arg(n - 1)                                 load/store(-(nArgs - 1))
//                     arg(n - 2)                                 load/store(-(nArgs - 2))
//                     ...                                        ...
//                     arg(1)                                     load/store(-1)
//                     function, which is arg(0)                  load/store(0)
//               fp -> nArgs                                      load/store(1)
//                     oldFp                                      load/store(2)
//                     oldIpb                                     load/store(3)
//                     oldIp                                      load/store(4)

#define DEBUG 1

typedef unsigned char byte_t;
typedef int           value_t;

value_t nil, stack, sp, globals, ipb, ip, fp, internedStringsRef, testMethod;

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
  value_t class;
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

value_t *slots(value_t oop) {
  assert(isOop(oop));
  return OT[OopValue(oop)].ptr.slots;
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

#define ref(a)     ({ value_t _r = mk(1); slotAtPut(_r, Int(0), a);                           _r; })
#define cons(a, b) ({ value_t _r = mk(2); slotAtPut(_r, Int(0), a); slotAtPut(_r, Int(1), b); _r; })

void addGlobal(value_t v) {
  slotAtPut(globals, Int(0), v);
  globals = cons(Int(0), globals);
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

/*
value_t lookup(value_t cls, value_t sel) {
  for (int idx = 0; idx < IntValue(Obj(cls).ptr.asClass->numSels); idx++)
    if (slotAt(Obj(cls).ptr.asClass->sels, Int(idx)) == sel)
      return slotAt(Obj(cls).ptr.asClass->impls, Int(idx));
  if (Obj(cls).ptr.asClass->super != nil)
    return lookup(Obj(cls).ptr.asClass->super, sel);
  printf("---------\n"); println(sel);
  error("^^ message not understood ^^");
  return nil;
}
*/

value_t store(value_t offset, value_t v) { return slotAtPut(stack, Int(IntValue(fp)- IntValue(offset)), v); }
value_t load (value_t offset)            { return slotAt(stack, Int(IntValue(fp) - IntValue(offset))); }

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

Instruction(iBox, _)           return iPush(1, ref(iPop(1, nil))); }
Instruction(iUnbox, _)         return iPush(1, slotAt(iPop(1, nil), Int(0))); }

Instruction(iLd, offset)       return iPush(1, slotAt(stack, Int(IntValue(fp) - IntValue(offset)))); }
Instruction(iSt, offset)       return slotAtPut(stack, Int(IntValue(fp) - IntValue(offset)), iPop(1, nil)); }

Instruction(iArg, n)           return iPush(1, load(Int(-IntValue(n)))); }

Instruction(iFv, n)            value_t closure = slotAt(load(Int(0)), Int(0));
                               return iPush(1, slotAt(closure, Int(IntValue(n) + 1))); }

Instruction(iStVar, _)         value_t val = iPop(1, nil);
                               return slotAtPut(iPop(1, nil), Int(0), val); }

Instruction(iMkFun, nFreeVars) value_t closure = mk(IntValue(nFreeVars) + 1);
                               for (int i = IntValue(nFreeVars); i >= 0; i--)
                                 slotAtPut(closure, Int(i), iPop(1, nil));
                               return iPush(1, closure); }

Instruction(iPrepCall, _)      iPush(1, nil); // make room for ip
                               iPush(1, ipb);
                               iPush(1, fp);
                               iPush(1, nil); // make room for nArgs
                               return nil; }

Instruction(iCall, nArgs)      ipb = slotAt(slotAt(slotAt(stack, Int(IntValue(sp) - 1 - IntValue(nArgs))), Int(0)), Int(0)); // code
                               fp  = Int(IntValue(sp) - IntValue(nArgs) - 1);
                               store(Int(1), nArgs);
                               store(Int(4), ip);
                               ip  = Int(-1);
                               return nil; }

Instruction(iTCall, newNArgs)  for (int i = IntValue(newNArgs); i >= 0; i--)
                                 store(Int(-i), iPop(1, nil));
                               ipb = slotAt(slotAt(load(Int(0)), Int(0)), Int(0));
                               ip  = Int(-1);
                               sp  = Int(IntValue(fp) + IntValue(newNArgs) + 1);
                               return nil; }

Instruction(iSend, nArgs)      // TODO: make this real
                               ipb = slotAt(testMethod, Int(0)); // get the code out of the closure
                               store(Int(0), ref(testMethod));   // box the closure
                               fp  = Int(IntValue(sp) - IntValue(nArgs) - 1);
                               store(Int(1), nArgs);
                               store(Int(4), ip);
                               ip  = Int(-1);
                               ip = Int(-1);
                               return nil; }

Instruction(iRet, _)           value_t r = iPop(1, nil);
                               sp    = Int(IntValue(fp) - 1);
                               fp    = iPop(1, nil);
                               ipb   = iPop(1, nil);
                               ip    = iPop(1, nil);
                               return iPush(1, r); }

Instruction(iJmp, n)           ip = Int(IntValue(ip) + IntValue(n)); return nil; }
Instruction(iJz,  n)           return IntValue(iPop(1, nil)) == 0 ? iJmp(1, n) : nil; }
Instruction(iJnz, n)           return IntValue(iPop(1, nil)) != 0 ? iJmp(1, n) : nil; }

enum {oArg, oFV, oStVar, oEq, oAdd, oSub, oMul, oMkFun, oPrepCall, oCall, oTCall, oSend, oRet, oPush, oPop, oBox, oUnbox,
      oJmp, oJZ, oJNZ, oHalt};
value_t (*jumpTable[])(int, value_t) =
     {iArg, iFv, iStVar, iEq, iAdd, iSub, iMul, iMkFun, iPrepCall, iCall, iTCall, iSend, iRet, iPush, iPop, iBox, iUnbox,
      iJmp, iJz, iJnz};

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

#define Push(X)  cons(Int(oPush),     Int(X))
#define MkFun(N) cons(Int(oMkFun),    Int(N))
#define PrepCall cons(Int(oPrepCall), nil)
#define Call(N)  cons(Int(oCall),     Int(N))
#define TCall(N) cons(Int(oTCall),    Int(N))
#define Send(N)  cons(Int(oSend),     Int(N))
#define Ret      cons(Int(oRet),      nil)
#define Arg(N)   cons(Int(oArg),      Int(N))
#define FV(O)    cons(Int(oFV),       Int(O))
#define StVar    cons(Int(oStVar),    nil)
#define Halt     cons(Int(oHalt),     nil)
#define Eq       cons(Int(oEq),       nil)
#define Add      cons(Int(oAdd),      nil)
#define Sub      cons(Int(oSub),      nil)
#define Mul      cons(Int(oMul),      nil)
#define Box      cons(Int(oBox),      nil)
#define Unbox    cons(Int(oUnbox),    nil)
#define Jmp(O)   cons(Int(oJmp),      Int(O))
#define JZ(O)    cons(Int(oJZ),       Int(O))
#define JNZ(O)   cons(Int(oJNZ),      Int(O))

/* Print all contents in the object table. */
void printOT() {
  for (int i = 0; i < OTSize; i++) {
    OTEntry *e = &OT[i];
    printf("%d:", i);
    if (e->numSlots == -1) {
      int next = e->ptr.next - OT;
      printf(" free -> %d\n", next >= 0 ? next : -1);
    }
    else {
      printf(" class=[(%d)], slots=", OopValue(e->class)); // classes are show in []s
      for (int n = 0; n < e->numSlots; n++) {
        value_t v = e->ptr.slots[n];
        if (isInt(v))
          printf(" %d", IntValue(v));                      // ints are shown as 123
        else
          printf(" (%d)", OopValue(v));                    // references are shown as (123)
      }
      printf("\n");
    }
  }
}

value_t stringify(char *s) {
  int size = strlen(s) + 1, idx = 0;
  value_t r = mk(size);
  while (1) {
    slotAtPut(r, Int(idx), Int(*s));
    if (*s == 0)
      break;
    s++; idx++;
  }
  return r;
}

value_t strCmp(value_t s1, value_t s2) {
  int idx = 0;
  while (1) {
    int c1 = IntValue(slotAt(s1, Int(idx))), c2 = IntValue(slotAt(s2, Int(idx))), diff = c1 - c2;
    if (diff != 0)
      return Int(diff);
    else if (c1 == 0)
      return Int(0);
    idx++;
  }
}

value_t intern(value_t s) {
  value_t internedStrings = slotAt(internedStringsRef, Int(0)), curr = internedStrings;
  while (curr != nil) {
    value_t is = slotAt(curr, Int(0));
    if (strCmp(s, is) == Int(0))
      return is;
    curr = slotAt(curr, Int(1));
  }
  iPush(1, s); // this Push and the Pop below are needed in case s is not already on the stack
  slotAtPut(internedStringsRef, Int(0), cons(s, internedStrings));
  iPop(1, nil);
  return s; 
}

void printString(value_t s) {
  int idx = 0;
  while (1) {
    int c = IntValue(slotAt(s, Int(idx++)));
    if (c == 0)
      break;
    printf("%c", c);
  } 
}

void printInternedStrings(void) {
  value_t curr = slotAt(internedStringsRef, Int(0));
  while (curr != nil) {
    value_t s = slotAt(curr, Int(0));
    printf("%d: ``", OopValue(s));
    printString(s);
    printf("''\n");
    curr = slotAt(curr, Int(1));
  }
}

void init(void) {
  OTSize = 0;
  growOT();
  globals = cons(Int(0), Int(0));
  addGlobal(nil = mk(0));
  addGlobal(stack = mk(10240));
  addGlobal(internedStringsRef = ref(nil));

/*
  value_t clsObj;
  addGlobal(clsObj = mk(4));
  Obj(clsObj).ptr.asClass->super   = nil;
  Obj(clsObj).ptr.asClass->numSels = 0;
  Obj(clsObj).ptr.asClass->sels    = mk(10);
  Obj(clsObj).ptr.asClass->impls   = mk(10);
*/

  addGlobal(testMethod = ref(nil));
  value_t testMethodCode = slotAtPut(testMethod, Int(0), mk(2));
  slotAtPut(testMethodCode, Int(0), Push(1234));
  slotAtPut(testMethodCode, Int(1), Ret);

  sp = Int(0);
}

int main(void) {
  init();

/*
  char s[1024];
  while (fgets(s, 1024, stdin) != NULL) {
    s[strlen(s) - 1] = 0;
    printf("=> oop %d\n", OopValue(intern(stringify(s))));
  }
  printInternedStrings();
*/

value_t prog = mk(11);
addGlobal(prog);
value_t sel = intern(stringify("aMethod"));
slotAtPut(prog, Int(0), PrepCall);
slotAtPut(prog, Int(1), cons(Int(oPush), sel));
slotAtPut(prog, Int(2), Box);
slotAtPut(prog, Int(3), Push(1));
slotAtPut(prog, Int(4), Box);
slotAtPut(prog, Int(5), Push(2));
slotAtPut(prog, Int(6), Box);
slotAtPut(prog, Int(7), Push(3));
slotAtPut(prog, Int(8), Box);
slotAtPut(prog, Int(9), Send(3));
slotAtPut(prog, Int(10), Halt);

  interp(prog);
  return 0;
}

