#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

// TODO: make this stuff OO (even the OT, ref-cells used for fvs and args), make "global obj", add recv to stack frame, etc.
// TODO: make strings instances of String, made up of instances of Char
// TODO: make a "CheapDictionary" class, use that for vtable
// TODO: use the same hashtable impl for method cache, interned strings dict., etc.
// TODO: remove redundant asserts
 
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

const int DEBUG = 1;

typedef unsigned char byte_t;
typedef int           value_t;

value_t nil, stack, sp, globals, ipb, ip, fp, internedStringsRef, cObject;

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
  value_t numSlots, _class;
  union {
    value_t        *slots;
    struct OTEntry *next;
  } ptr;
} OTEntry;

const size_t OrigOTSize = 2; // must be >= 2
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
    newOT[i].numSlots = Int(-1);
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

value_t classOf(value_t x) {
  return isOop(x) ? OT[OopValue(x)]._class : cObject;
}

value_t numSlots(value_t oop) {
  assert(isOop(oop));
  return OT[OopValue(oop)].numSlots;
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

value_t mk(size_t numSlots);
value_t intern(value_t s);

#define ref(a)     ({ value_t _r = mk(1); slotAtPut(_r, Int(0), a);                           _r; })
#define cons(a, b) ({ value_t _r = mk(2); slotAtPut(_r, Int(0), a); slotAtPut(_r, Int(1), b); _r; })

value_t addGlobal(value_t v) {
  slotAtPut(globals, Int(0), v);
  globals = cons(nil, globals);
  return v;
}

typedef struct { value_t name, slotNames, numSlots, vTableSize, sels, impls, super; } classSlots;

classSlots *asClass(value_t oop) {
  assert(isOop(oop));
  assert(numSlots(oop) == Int(sizeof(classSlots) / sizeof(value_t))); // TODO: make this an instanceof check
  return (classSlots *)slots(oop);
}

value_t installMethod(value_t _class, value_t sel, value_t impl) {
  classSlots *cls = asClass(_class);
  int freeIdx = -1;
  for (int idx = 0; idx < IntValue(cls->numSlots); idx++) {
    value_t s = slotAt(cls->sels, Int(idx));
    if      (s == sel) return slotAtPut(cls->impls, Int(idx), impl);
    else if (s == nil) freeIdx = idx;
  }
  if (freeIdx >= 0) {        slotAtPut(cls->sels,  Int(freeIdx), sel);
                      return slotAtPut(cls->impls, Int(freeIdx), impl); }
  int oldVTableSize = IntValue(cls->vTableSize), newVTableSize = oldVTableSize * 2;
  cls->vTableSize = Int(newVTableSize);
  value_t arr = mk(newVTableSize); memcpy(slots(arr), slots(cls->sels),  newVTableSize * sizeof(value_t)); cls->sels  = arr;
          arr = mk(newVTableSize); memcpy(slots(arr), slots(cls->impls), newVTableSize * sizeof(value_t)); cls->impls = arr;
         slotAtPut(cls->sels,  Int(oldVTableSize), sel);
  return slotAtPut(cls->impls, Int(oldVTableSize), impl);
}

value_t mkClass(value_t name, value_t slotNames, value_t super) {
  value_t _class   = addGlobal(mk(sizeof(classSlots) / sizeof(value_t)));
  classSlots *cls = asClass(_class);
  cls->name       = intern(name);
  cls->slotNames  = slotNames;
  cls->numSlots   = super == nil ? Int(0)  : asClass(super)->numSlots;
  cls->vTableSize = Int(16);
  cls->sels       = mk(IntValue(cls->vTableSize));
  cls->impls      = mk(IntValue(cls->vTableSize));
  cls->super      = super;
  while (slotNames != nil) {
    // TODO: install getter and setter for this slot
    cls->numSlots = Int(IntValue(cls->numSlots) + 1);
    slotNames = slotAt(slotNames, Int(1));
  }
  return _class;
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
  int n = IntValue(e.numSlots);
  while (n--)
    r += mark(*(slot++));
  return r;
}

size_t gc(void) {
  memset(marked, 0, OTSize);
  int numMarked = mark(globals);
  for (int i = 0; i < OTSize; i++) {
    if (marked[i])
      continue;
    free(OT[i].ptr.slots);
    OT[i].numSlots  = Int(-1);
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
  newGuy->numSlots = Int(numSlots);
  newGuy->_class = cObject;
  newGuy->ptr.slots = allocate(numSlots, value_t);
  return Oop(newGuy - OT);
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

void printString(value_t s);

value_t lookup(value_t _class, value_t sel) {
  classSlots *cls = asClass(_class);
  for (int idx = 0; idx < IntValue(cls->vTableSize); idx++)
    if (slotAt(cls->sels, Int(idx)) == sel)
      return slotAt(cls->impls, Int(idx));
  if (cls->super != nil)
    return lookup(cls->super, sel);
  printf("\nselector: "); printString(sel); putchar('\n');
  error("^^ message not understood ^^");
  return nil;
}

const size_t MaxNumPrims = 32;
value_t (*prims[MaxNumPrims])(int, value_t);
size_t numPrims = 0;

value_t addPrim(value_t (*f)(int, value_t)) { assert(numPrims < MaxNumPrims);
                                              prims[numPrims] = f;
                                              return Int(numPrims++); }

value_t store(value_t offset, value_t v)    { return slotAtPut(stack, Int(IntValue(fp)- IntValue(offset)), v); }
value_t load (value_t offset)               { return slotAt(stack, Int(IntValue(fp) - IntValue(offset)));      }


#define Prim(Name, Arg, Body) value_t p##Name(int quiet, value_t Arg) {                          \
                                if (DEBUG && !quiet) { printf(">>> " #Name " "); println(Arg); } \
                                Body                                                             \
                              }                                                                  \
                              value_t Name = addPrim(p##Name);

Prim(Push, v,          { slotAtPut(stack, sp, v);
                         sp = Int(IntValue(sp) + 1);
                         return v; })

Prim(Pop, _,           { assert(sp > Int(0));
                         sp = Int(IntValue(sp) - 1);
                         value_t r = slotAt(stack, sp);
                         slotAtPut(stack, sp, Int(0));
                         return r; })

Prim(Eq, _,            { return pPush(1, Int(IntValue(pPop(1, nil)) == IntValue(pPop(1, nil)))); })

Prim(Add, _,           { value_t op2 = pPop(1, nil);
                         return pPush(1, Int(IntValue(pPop(1, nil)) + IntValue(op2))); })
Prim(Sub, _,           { value_t op2 = pPop(1, nil);
                         return pPush(1, Int(IntValue(pPop(1, nil)) - IntValue(op2))); })
Prim(Mul, _,           { value_t op2 = pPop(1, nil);
                         return pPush(1, Int(IntValue(pPop(1, nil)) * IntValue(op2))); })

Prim(Box, _,           { return pPush(1, ref(pPop(1, nil))); })
Prim(Unbox, _,         { return pPush(1, slotAt(pPop(1, nil), Int(0))); })

Prim(Ld, offset,       { return pPush(1, slotAt(stack, Int(IntValue(fp) - IntValue(offset)))); })
Prim(St, offset,       { return slotAtPut(stack, Int(IntValue(fp) - IntValue(offset)), pPop(1, nil)); })

Prim(Arg, n,           { return pPush(1, load(Int(-IntValue(n)))); })
Prim(Fv, n,            { value_t closure = slotAt(load(Int(0)), Int(0));
                         return pPush(1, slotAt(closure, Int(IntValue(n) + 1))); })

Prim(StVar, _,         { value_t val = pPop(1, nil);
                         return slotAtPut(pPop(1, nil), Int(0), val); })

Prim(MkFun, nFreeVars, { value_t closure = mk(IntValue(nFreeVars) + 1);
                         for (int i = IntValue(nFreeVars); i >= 0; i--)
                           slotAtPut(closure, Int(i), pPop(1, nil));
                         return pPush(1, closure); })

Prim(PrepCall, _,      { pPush(1, nil); // make room for ip
                         pPush(1, ipb);
                         pPush(1, fp);
                         pPush(1, nil); // make room for nArgs
                         return nil; })

Prim(Call, nArgs,      { ipb = slotAt(slotAt(slotAt(stack, Int(IntValue(sp) - 1 - IntValue(nArgs))), Int(0)), Int(0)); // code
                         fp  = Int(IntValue(sp) - IntValue(nArgs) - 1);
                         store(Int(1), nArgs);
                         store(Int(4), ip);
                         ip  = Int(-1);
                         return nil; })

Prim(TCall, newNArgs,  { for (int i = IntValue(newNArgs); i >= 0; i--)
                           store(Int(-i), pPop(1, nil));
                         ipb = slotAt(slotAt(load(Int(0)), Int(0)), Int(0));
                         ip  = Int(-1);
                         sp  = Int(IntValue(fp) + IntValue(newNArgs) + 1);
                         return nil; })

Prim(Send, nArgs,      { fp = Int(IntValue(sp) - IntValue(nArgs) - 1);
                         value_t recv   = slotAt(load(Int(-1)), Int(0));                       // unbox arg(1)
                         value_t method = lookup(classOf(recv), slotAt(load(Int(0)), Int(0))); // unbox the selector, do lookup
                         store(Int(0), ref(method));                                           // box the closure
                         store(Int(1), nArgs);
                         store(Int(4), ip);
                         ipb = slotAt(method, Int(0));                                         // get the code out of the closure
                         ip = Int(-1);
                         return nil; })

Prim(Ret, _,           { value_t r = pPop(1, nil);
                         sp  = Int(IntValue(fp) - 1);
                         fp  = pPop(1, nil);
                         ipb = pPop(1, nil);
                         ip  = pPop(1, nil);
                         return pPush(1, r); })

Prim(Jmp, n,           { ip = Int(IntValue(ip) + IntValue(n)); return nil;      })
Prim(Jz,  n,           { return IntValue(pPop(1, nil)) == 0 ? pJmp(1, n) : nil; })
Prim(Jnz, n,           { return IntValue(pPop(1, nil)) != 0 ? pJmp(1, n) : nil; })

Prim(Halt, _,          { })

void interp(value_t prog) {
  fp  = sp;
  ipb = prog;
  ip  = Int(0);
  while (1) {
    value_t instr = slotAt(ipb, ip), primIdx = IntValue(slotAt(instr, Int(0))), op = slotAt(instr, Int(1));
    if (DEBUG) { printf("\n\n\n"); printState(); printf("\n"); }
    if (0 <= primIdx && primIdx < sizeof(prims) / sizeof(value_t (*)(int, value_t))) prims[primIdx](0, op);
    else                                                                             error("invalid primitive %d\n", primIdx);
    ip = Int(IntValue(ip) + 1);
    if (DEBUG) { printf("\n"); printState(); printf("\n\n\n"); }
    if (primIdx == IntValue(Halt))
      break;
  }
}

/* Print all contents in the object table. */
void printOT() {
  for (int i = 0; i < OTSize; i++) {
    OTEntry *e = &OT[i];
    printf("%d:", i);
    if (IntValue(e->numSlots) == -1) {
      int next = e->ptr.next - OT;
      printf(" free -> %d\n", next >= 0 ? next : -1);
    }
    else {
      printf(" class=[(%d)], slots=", OopValue(e->_class)); // classes are show in []s
      for (int n = 0; n < IntValue(e->numSlots); n++) {
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
  pPush(1, s); // this Push and the Pop below are needed in case s is not already on the stack
  slotAtPut(internedStringsRef, Int(0), cons(s, internedStrings));
  pPop(1, nil);
  return s; 
}

void printString(value_t s) {
  int idx = 0;
  while (1) {
    int c = IntValue(slotAt(s, Int(idx++)));
    if (c == 0)
      break;
    putchar(c);
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
  sp = Int(0);
  nil = mk(0);
  globals = cons(nil, nil);
  stack = addGlobal(mk(10240));
  internedStringsRef = addGlobal(ref(nil));

  value_t name = intern(stringify("Object"));
  cObject = mkClass(name, nil, nil);
  for (int idx = 0; idx < OTSize; idx++) {
    if (IntValue(OT[idx].numSlots) < 0)
      continue;
    OT[idx]._class = cObject;
  }

  value_t testMethod     = addGlobal(ref(nil)),
          testMethodCode = slotAtPut(testMethod, Int(0), mk(2));
  slotAtPut(testMethodCode, Int(0), cons(Push, Int(1234)));
  slotAtPut(testMethodCode, Int(1), cons(Ret, nil));
  value_t sel = intern(stringify("aMethod"));
  installMethod(cObject, sel, testMethod);

}

int main(void) {
  init();

  value_t sel = intern(stringify("aMethod"));

  value_t prog = addGlobal(mk(11));
  slotAtPut(prog, Int(0),  cons(PrepCall, nil));
  slotAtPut(prog, Int(1),  cons(Push,     sel));
  slotAtPut(prog, Int(2),  cons(Box,      nil));
  slotAtPut(prog, Int(3),  cons(Push,     Int(1)));
  slotAtPut(prog, Int(4),  cons(Box,      nil));
  slotAtPut(prog, Int(5),  cons(Push,     Int(2)));
  slotAtPut(prog, Int(6),  cons(Box,      nil));
  slotAtPut(prog, Int(7),  cons(Push,     Int(3)));
  slotAtPut(prog, Int(8),  cons(Box,      nil));
  slotAtPut(prog, Int(9),  cons(Send,     Int(3)));
  slotAtPut(prog, Int(10), cons(Halt,     nil));

  interp(prog);

  return 0;
}

