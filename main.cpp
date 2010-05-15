#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

// TODO: make characters be instances of Char, not just Ints
// TODO: syntactic sugar: <- is a low-priority "there's another argument" next, e.g., myArray at: 5 <- 6
// TODO: make a "CheapDictionary" class, use it for vtables, prims, globals, etc.
// TODO: make everything OO (the OT, ref-cells used for FVs and args, etc.)
// TODO: add a primitive that replaces the implementation of a primitive with a method (for bootstrapping)
 
// Stack Layout:       ... local vars, etc. ...
//                     arg(n)                        load/store(-nArgs)
//                     arg(n - 1)                    load/store(-(nArgs - 1))
//                     arg(n - 2)                    load/store(-(nArgs - 2))
//                     ...                           ...
//                     arg(1)                        load/store(-1)
//                     function, which is arg(0)     load/store(0)
//               fp -> nArgs                         load/store(1)
//                     oldFp                         load/store(2)
//                     oldIpb                        load/store(3)
//                     oldIp                         load/store(4)

int debug = 0;

typedef unsigned char byte_t;
typedef int           value_t;

value_t nil, stack, sp, globals, ipb, ip, fp, internedStringsRef,                        // registers, etc.
        Obj, Nil, Int, Char, Str, Var, Closure, Class,                                   // "classes", i.e., "primordial instances"
        sIdentityHash, sPrint, sPrintln, sAdd, sSub, sMul;                               // selectors

#define allocate(N, T) ((T *) calloc(N, sizeof(T)))                                      // calloc fills memory w/ 0s, i.e., nils

#define isInt(X)            ((X) & 1)                                                    // integers are tagged (lsb = 1)
#define Int(X)              (((X) << 1) | 1)
#define IntValue(X)         ({ value_t _x = X; if (debug) assert(isInt(_x)); _x >> 1; })

#define isOop(X)            (((X) & 1) == 0)
#define Oop(X)              ((X) << 1)
#define OopValue(X)         ({ value_t _x = X; if (debug) assert(isOop(_x)); _x >> 1; })

void error(char *fmt, ...)  { va_list args;
                              va_start(args, fmt);
                              fprintf(stderr, "error: ");
                              vfprintf(stderr, fmt, args);
                              fputc('\n', stderr);
                              exit(1); }

typedef struct OTEntry { value_t numSlots, cls;
                         union { value_t *slots;
                                 struct OTEntry *next; } ptr;                               } OTEntry;

typedef struct         { value_t name, slotNames, numSlots, vTableSize, sels, impls, super; } classSlots;

const size_t OrigOTSize = 2; // must be >= 2
size_t OTSize = 0;
OTEntry *OT, *freeList;
byte_t *marked;

void growOT(void) {
  size_t  newOTSize    = OTSize > 0 ? OTSize * 2 : OrigOTSize;
  if (debug) printf("growOT, new size is %li\n", newOTSize);
  OTEntry *newOT       = allocate(newOTSize, OTEntry);
  byte_t  *newMarked   = allocate(newOTSize, byte_t);
  byte_t  *newIsGlobal = allocate(newOTSize, byte_t);
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

value_t mk(size_t numSlots);

#define deref(r)                       slotAt   (r, Int(0))
#define deref_(r, v)                   slotAtPut(r, Int(0), v)
#define ref(a)                         ({ value_t _a = a, _r = mk(1); deref_(_r, _a); _r; })
#define car(cc)                        slotAt   (cc, Int(0))
#define car_(cc, v)                    slotAtPut(cc, Int(0), v)
#define cdr(cc)                        slotAt   (cc, Int(1))
#define cdr_(cc, v)                    slotAtPut(cc, Int(1), v)
#define cons(a, b)                     ({ value_t _a = a, _b = b, _r = mk(2); car_(_r, _a); cdr_(_r, _b); _r; })

#define slotAt(oop, idx)               ({ value_t _oop = OopValue(oop), _idx = IntValue(idx);             \
                                          assert(0 <= _idx && _idx < IntValue(OT[_oop].numSlots));        \
                                          OT[_oop].ptr.slots[_idx]; })

#define slotAtPut(oop, idx, val)       ({ value_t _oop = OopValue(oop), _idx = IntValue(idx), _val = val; \
                                          assert(0 <= _idx && _idx < IntValue(OT[_oop].numSlots));        \
                                          OT[_oop].ptr.slots[_idx] = _val; })

value_t numSlots(value_t oop)           { assert(isOop(oop));
                                          return OT[OopValue(oop)].numSlots; }

value_t *slots(value_t oop)             { assert(isOop(oop));
                                          return OT[OopValue(oop)].ptr.slots; }

value_t classOf(value_t x)              { return isInt(x) ? Int : OT[OopValue(x)].cls;       }
value_t classOf_(value_t x, value_t c)  { assert(!isInt(x)); return OT[OopValue(x)].cls = c; }

classSlots *asClass(value_t oop)        { assert(isOop(oop));
                                          // TODO: replace the following assert with an instanceof (or at least class) check
                                          assert(numSlots(oop) == Int(sizeof(classSlots) / sizeof(value_t)));
                                          return (classSlots *)slots(oop); }

value_t addGlobal(value_t v)            { car_(globals, v);
                                          globals = cons(nil, globals);
                                          return v; }

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
    OT[i].numSlots = Int(-1);
    OT[i].ptr.next = freeList;
    freeList       = &OT[i];
  }
  if (debug) printf("GC reclaimed %ld OTEntries\n", OTSize - numMarked);
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
  newGuy->numSlots  = Int(numSlots);
  newGuy->cls       = Obj;
  newGuy->ptr.slots = allocate(numSlots, value_t);
  return Oop(newGuy - OT);
}

void _print(value_t v, value_t n = Int(0), value_t selIdx = Int(-1)) {
  if      (v == nil) printf("nil");
  else if (isInt(v)) printf("%d", IntValue(v));
  else if (isOop(v)) { printf("[");
                       if (IntValue(n) > 5) printf("...");
                       else                 for (int i = 0; i < IntValue(numSlots(v)); i++) {
                                              if (i > 0) printf(", ");
                                              if (i == IntValue(selIdx)) printf("<<<");
                                              _print(slotAt(v, Int(i)), Int(IntValue(n) + 1), -1);
                                              if (i == IntValue(selIdx)) printf(">>>");
                                            }
                       printf("]");
                     }
  else               error("print doesn't know how to handle value (%d)\n", v);
}

void print(value_t v)   { _print(v);               }
void println(value_t v) { print(v); putchar('\n'); }

const size_t MaxNumPrims = 64;
value_t (*prims[MaxNumPrims])(value_t);
void *primNames[MaxNumPrims];
size_t numPrims = 0;

value_t addPrim(char *n, value_t (*f)(value_t)) { assert(numPrims < MaxNumPrims);
                                                        prims[numPrims] = f;
                                                  primNames[numPrims] = n;
                                                  return Int(numPrims++); }

value_t store(value_t offset, value_t v)        { return slotAtPut(stack, Int(IntValue(fp) - IntValue(offset)), v); }
value_t load (value_t offset)                   { return slotAt   (stack, Int(IntValue(fp) - IntValue(offset)));    }


#define Prim(Name, Arg, Body)       value_t p##Name(value_t Arg) { Body; return nil; } \
                                    value_t Name = addPrim(#Name, p##Name);

#define _p(Name)                                                         prims[IntValue(Name)](nil)
#define _p1(Name, Arg)                                                   prims[IntValue(Name)](Arg)
#define _p2(Name, Arg1, Arg2)       ({                  _p1(Push, Arg2); prims[IntValue(Name)](Arg1); })
#define _p3(Name, Arg1, Arg2, Arg3) ({ _p1(Push, Arg3); _p1(Push, Arg2); prims[IntValue(Name)](Arg1); })

Prim(Push, v,          { value_t _v = v;
                         slotAtPut(stack, sp, _v);
                         sp = Int(IntValue(sp) + 1);
                         return _v; })

Prim(Pop, _,           { assert(sp > Int(0));
                         sp = Int(IntValue(sp) - 1);
                         value_t r = slotAt(stack, sp);
                         slotAtPut(stack, sp, nil);     // clear this slot to prevent memory leak
                         return r; })

/*
Prim(SlotAt,    recv,  { value_t idx = _p(Pop);                        return slotAt   (recv, idx);      })
Prim(SlotAtPut, recv,  { value_t idx = _p(Pop); value_t val = _p(Pop); return slotAtPut(recv, idx, val); })
*/

Prim(Eq, _,            { return _p1(Push, Int(IntValue(_p(Pop)) == IntValue(_p(Pop)))); })

Prim(Add, _,           { value_t op2 = _p(Pop); return _p1(Push, Int(IntValue(_p(Pop)) + IntValue(op2))); })
Prim(Sub, _,           { value_t op2 = _p(Pop); return _p1(Push, Int(IntValue(_p(Pop)) - IntValue(op2))); })
Prim(Mul, _,           { value_t op2 = _p(Pop); return _p1(Push, Int(IntValue(_p(Pop)) * IntValue(op2))); })

Prim(Box, _,           { return _p1(Push, ref  (_p(Pop))); })
Prim(Unbox, _,         { return _p1(Push, deref(_p(Pop))); })

Prim(Ld, offset,       { return _p1(Push, slotAt   (stack, Int(IntValue(fp) - IntValue(offset))));         })
Prim(St, offset,       { return           slotAtPut(stack, Int(IntValue(fp) - IntValue(offset)), _p(Pop)); })

Prim(Arg, n,           { return _p1(Push, load(Int(-IntValue(n)))); })
Prim(Fv, n,            { value_t closure = slotAt(load(Int(0)), Int(0));
                         return _p1(Push, slotAt(closure, Int(IntValue(n) + 1))); })

Prim(StVar, _,         { value_t val = _p(Pop);
                         return deref_(_p(Pop), val); })

Prim(MkFun, nFreeVars, { value_t closure = mk(IntValue(nFreeVars) + 1);
                         for (int i = IntValue(nFreeVars); i >= 0; i--)
                           slotAtPut(closure, Int(i), _p(Pop));
                         return _p1(Push, closure); })

Prim(PrepCall, _,      { _p1(Push, nil); // make room for ip
                         _p1(Push, ipb);
                         _p1(Push, fp);
                         _p1(Push, nil); // make room for nArgs
                         return nil; })

Prim(Call, nArgs,      { ipb = deref(slotAt(slotAt(stack, Int(IntValue(sp) - 1 - IntValue(nArgs))), Int(0))); // unbox fn & get code
                         fp  = Int(IntValue(sp) - IntValue(nArgs) - 1);
                         store(Int(1), nArgs);
                         store(Int(4), ip);
                         ip  = Int(-1);
                         return nil; })

Prim(TCall, newNArgs,  { for (int i = IntValue(newNArgs); i >= 0; i--)
                           store(Int(-i), _p(Pop));
                         ipb = slotAt(deref(load(Int(0))), Int(0));
                         ip  = Int(-1);
                         sp  = Int(IntValue(fp) + IntValue(newNArgs) + 1);
                         return nil; })

Prim(Ret, _,           { value_t r = _p(Pop);
                         sp  = Int(IntValue(fp) - 1);
                         fp  = _p(Pop);
                         ipb = _p(Pop);
                         ip  = _p(Pop);
                         return _p1(Push, r); })

Prim(InstMeth, cls,    { value_t sel      = _p(Pop);
                         value_t impl     = _p(Pop);
                         classSlots *_cls = asClass(cls);
                         int freeIdx = -1;
                         for (int idx = 0; idx < IntValue(_cls->vTableSize); idx++) {
                           value_t s = slotAt(_cls->sels, Int(idx));
                           if      (s == sel) return slotAtPut(_cls->impls, Int(idx), impl);
                           else if (s == nil) freeIdx = idx;
                         }
                         if (freeIdx >= 0) {        slotAtPut(_cls->sels,  Int(freeIdx), sel);
                                             return slotAtPut(_cls->impls, Int(freeIdx), impl); }
                         int oldVTSize = IntValue(_cls->vTableSize);
                         int newVTSize = oldVTSize * 2;
                         _cls->vTableSize = Int(newVTSize);
                         value_t m;
                         m = mk(newVTSize); memcpy(slots(m), slots(_cls->sels),  newVTSize * sizeof(value_t)); _cls->sels  = m;
                         m = mk(newVTSize); memcpy(slots(m), slots(_cls->impls), newVTSize * sizeof(value_t)); _cls->impls = m;
                                slotAtPut(_cls->sels,  Int(oldVTSize), sel);
                         return slotAtPut(_cls->impls, Int(oldVTSize), impl); })

Prim(ObjGetSet, recv,  { value_t nArgs = load(Int(1)); // the number of arguments passed to the method, not the primitive
                         value_t idx   = _p(Pop);
                         switch (IntValue(nArgs)) {
                           case 1:  return slotAt   (recv, idx);
                           case 2:  return slotAtPut(recv, idx, deref(load(Int(-2))));
                           default: error("getter/setter called with %d arguments (must be 1 or 2)", IntValue(nArgs));
                         } })

Prim(DoPrim, n,        { value_t prim = _p(Pop);
                         value_t arg1 = n > Int(0) ? _p(Pop) : nil;
                         return _p1(Push, _p1(prim, arg1)); })

Prim(InstGetSet, cls,  { value_t name     = _p(Pop);
                         value_t idx      = _p(Pop);
                         classSlots *_cls = asClass(cls);
                                            slotAtPut(_cls->sels,  idx, name);
                         value_t closure  = slotAtPut(_cls->impls, idx, ref(nil));
                         value_t code     = deref_(closure, mk(6));
                         slotAtPut(code, Int(0), cons(Push,   idx));
                         slotAtPut(code, Int(1), cons(Arg,    Int(1)));    // push boxed receiver
                         slotAtPut(code, Int(2), cons(Unbox,  nil));       // unbox the receiver on the stack
                         slotAtPut(code, Int(3), cons(Push,   ObjGetSet)); // push the primitive
                         slotAtPut(code, Int(4), cons(DoPrim, Int(2)));
                         slotAtPut(code, Int(5), cons(Ret,    nil));       // return (DoPrim's result is top of stack)
                       })

Prim(MkClass, name,    { value_t cls       = addGlobal(mk(sizeof(classSlots) / sizeof(value_t)));
                         classSlots *_cls  = asClass(cls);
                         _cls->name        = name;
                         _cls->super       = _p(Pop);
                         _cls->slotNames   = _p(Pop);
                         _cls->numSlots    = Int(IntValue(numSlots(_cls->slotNames)) +
                                                 IntValue(_cls->super == nil ? Int(0) : asClass(_cls->super)->numSlots));
                         _cls->vTableSize  = Int(16);
                         _cls->sels        = mk(IntValue(_cls->vTableSize));
                         _cls->impls       = mk(IntValue(_cls->vTableSize));
                         for (value_t idx = Int(0); idx < numSlots(_cls->slotNames); idx = Int(IntValue(idx) + 1))
                           _p3(InstGetSet, cls, slotAt(_cls->slotNames, idx), idx);
                         return cls; })

Prim(MkObj, cls,       { value_t nAddlSlots = _p(Pop);
                         value_t obj        = mk((cls == nil ? 0 : IntValue(asClass(cls)->numSlots)) + IntValue(nAddlSlots));
                         classOf_(obj, cls);
                         return obj; })

Prim(StrPrint, s,     { int idx = 0;
                        while (1) {
                          int c = IntValue(slotAt(s, Int(idx++)));
                          if (c == 0)
                            break;
                          putchar(c);
                        }
                        return s; })

Prim(Lookup, _,        { // the method cache should be implemented in "userland" (where this primitive will be replaced)
                         value_t recv = deref(load(Int(-1)));                            // unbox arg(1)
                         value_t sel  = deref(load(Int(0)));                             // unbox the selector
                         value_t cls  = classOf(recv);
                         while (cls != nil) {
                           classSlots *_cls = asClass(cls);
                           for (int idx = 0; idx < IntValue(_cls->vTableSize); idx++)
                             if (slotAt(_cls->sels, Int(idx)) == sel) {
                               value_t method = slotAt(_cls->impls, Int(idx));
                               deref_(load(Int(0)), method);                             // replace selector (in box) w/ closure
                               return method;
                             }
                           cls = _cls->super;
                         }
                         char *cStringify(value_t);
                         error("%s does not understand \"%s\"", cStringify(asClass(classOf(recv))->name), cStringify(sel));
                         return nil; })

Prim(Send, nArgs,      { fp = Int(IntValue(sp) - IntValue(nArgs) - 1);
                         store(Int(1), nArgs);
                         store(Int(4), ip);
                         value_t method = _p(Lookup);
                         ipb = slotAt(method, Int(0)); // get the code out of the closure
                         ip = Int(-1);
                         return ipb; })

Prim(Jmp, n,           { ip = Int(IntValue(ip) + IntValue(n));    })
Prim(JZ,  n,           { if (IntValue(_p(Pop)) == 0) _p1(Jmp, n); })
Prim(JNZ, n,           { if (IntValue(_p(Pop)) != 0) _p1(Jmp, n); })

Prim(Halt, _,          { })

void printState(void) {
  printf("ipb(ip="); print(ip); printf("): [");
  for (int idx = 0; idx < IntValue(numSlots(ipb)); idx++) {
    if (idx > 0) printf(", ");
    value_t instr = slotAt(ipb, Int(idx)), prim = slotAt(instr, Int(0)), arg = slotAt(instr, Int(1));
    if (idx == IntValue(ip)) printf("<<");
    _p1(StrPrint, (value_t)primNames[IntValue(prim)]); putchar('('); print(arg); putchar(')');
    if (idx == IntValue(ip)) printf(">>");
  }
  printf("]\n");
  printf("fp: "); println(fp);
  printf("/---------------------------------------------------------------------\\\n");
  int spv = IntValue(sp);
  while (spv-- > 0) { printf("  "); println(slotAt(stack, Int(spv))); }
  printf("\\---------------------------------------------------------------------/\n");
}

value_t interp(value_t prog, value_t retFp = Int(-1)) {
  ipb = prog;
  ip  = Int(0);
  while (1) {
    value_t instr = slotAt(ipb, ip), primIdx = IntValue(car(instr)), op = cdr(instr);
    if (debug) { puts("\n\n"); printState(); putchar('\n'); _p1(StrPrint, (value_t)primNames[primIdx]); putchar(' '); println(op); }
    if (0 <= primIdx && primIdx < numPrims) prims[primIdx](op);
    else                                    error("%d is not a valid primitive\n", primIdx);
    ip = Int(IntValue(ip) + 1);
    if (debug) { putchar('\n'); printState(); printf("\n\n\n"); }
    if (primIdx == IntValue(Halt))
      break;
    else if (primIdx == IntValue(Ret) && fp == retFp) {
      ip = Int(IntValue(ip) - 1); // undo increment of ip
      break;
    }
  }
  return _p(Pop);
}

#define PushArg(x)                   ({ _p1(Push, x); _p(Box);                         })
#define PrepSend(sel, recv)          ({ _p(PrepCall); PushArg(sel); PushArg(recv); fp; })
#define DoSend(n, retFp)             ({ _p1(Send, Int(n)); interp(ipb, retFp);         })

#define send1(sel, recv)             ({ value_t retFp = PrepSend(sel, recv);                               DoSend(1, retFp); })
#define send2(sel, recv, arg1)       ({ value_t retFp = PrepSend(sel, recv); PushArg(arg1);                DoSend(2, retFp); })
#define send3(sel, recv, arg1, arg2) ({ value_t retFp = PrepSend(sel, recv); PushArg(arg1); PushArg(arg2); DoSend(3, retFp); })

Prim(ObjIdentityHash, recv, { return Int(recv); })
Prim(IntIdentityHash, recv, { return Int(recv); })

Prim(Newline,     _,    { putchar('\n');                                            }) // TODO: replace w/ more general Char>>print
Prim(ObjPrint,    recv, { _p1(StrPrint, asClass(classOf(recv))->name); print(recv); })
Prim(NilPrint,    recv, { printf("nil");                                            })
Prim(IntPrint,    recv, { printf("%d", IntValue(recv));                             })
Prim(ObjPrintln,  recv, { send1(sPrint, recv); _p(Newline);                         })

Prim(PrintOT,     _,    { for (int i = 0; i < OTSize; i++) {
                            OTEntry *e = &OT[i];
                            printf("%d: ", i);
                            if (IntValue(e->numSlots) == -1) {
                              int next = e->ptr.next - OT;
                              printf("(free, next=%d)\n", next >= 0 ? next : -1);
                            }
                            else {
                              _p1(StrPrint, asClass(e->cls)->name); printf("[");
                              for (int n = 0; n < IntValue(e->numSlots); n++) {
                                value_t v = e->ptr.slots[n];
                                if (n > 0) printf(", ");
                                if (isInt(v)) printf("%d",   IntValue(v)); // ints are shown as 123
                                else          printf("(%d)", OopValue(v)); // references are shown as (123)
                              }
                              printf("]\n");
                            }
                          } })

Prim(IntAdd,      recv, { return Int(IntValue(recv) + IntValue(deref(_p1(Arg, Int(2))))); })
Prim(IntSub,      recv, { return Int(IntValue(recv) - IntValue(deref(_p1(Arg, Int(2))))); })
Prim(IntMul,      recv, { return Int(IntValue(recv) * IntValue(deref(_p1(Arg, Int(2))))); })

Prim(StrCmp, _,   { value_t s1 = _p(Pop);
                    value_t s2 = _p(Pop);
                    int idx = 0;
                    while (1) {
                      int c1   = IntValue(slotAt(s1, Int(idx)));
                      int c2   = IntValue(slotAt(s2, Int(idx)));
                      int diff = c1 - c2;
                      if      (diff != 0) return Int(diff);
                      else if (c1 == 0)   return Int(0);
                      idx++;
                    } })

Prim(Intern, s,   { value_t internedStrings = deref(internedStringsRef);
                    for (value_t curr = internedStrings; curr != nil; curr = cdr(curr)) {
                      value_t is = car(curr);
                      _p1(Push, is);
                      _p1(Push, s);
                      if (_p(StrCmp) == Int(0))
                        return is;
                    }
                    _p1(Push, s); // this Push and the Pop below are needed in case s is not already on the stack
                    deref_(internedStringsRef, cons(s, internedStrings));
                    _p(Pop);
                    return s; })

value_t stringify(char *s) {
  int idx = 0;
  value_t r = _p2(MkObj, Str, Int(strlen(s) + 1));
  while (1) {
    slotAtPut(r, Int(idx), Int(*s));
    if (*s == 0)
      break;
    s++; idx++;
  }
  return r;
}

char *cStringify(value_t s) {
  int n = IntValue(numSlots(s));
  char *r = (char *)malloc(n);
  for (int idx = 0; idx < n; idx++)
    r[idx] = IntValue(slotAt(s, Int(idx)));
  return r;
}

void installPrimAsMethod(value_t _class, value_t sel, value_t prim) {
  value_t closure = _p1(Push, ref(nil));
  value_t code    = deref_(closure, mk(5));
  slotAtPut(code, Int(0), cons(Arg,    Int(1))); // push boxed receiver
  slotAtPut(code, Int(1), cons(Unbox,  nil));    // unbox the receiver on the stack
  slotAtPut(code, Int(2), cons(Push,   prim));   // push the primitive
  slotAtPut(code, Int(3), cons(DoPrim, Int(1)));
  slotAtPut(code, Int(4), cons(Ret,    nil));    // return (DoPrim's result is top of stack)
  _p1(Push, sel);
  _p1(InstMeth, _class);
}

void init(int _debug) {
  debug   = _debug;
  OTSize  = 0;
  growOT();
  sp      = Int(0);
  ip      = Int(-1);
  nil     = mk(0);   // allocate nil before any other objects so it gets to be 0
  globals = cons(nil, nil);
  stack   = addGlobal(mk(10240));
  internedStringsRef = addGlobal(ref(nil));

  // "objectify" primNames (they were C strings up to this point)
  for (int p = 0; p < numPrims; p++)
    primNames[p] = (void *)_p1(Intern, stringify((char *)primNames[p]));

  sIdentityHash = _p1(Intern, stringify("identityHash"));
  sPrint        = _p1(Intern, stringify("print"));
  sPrintln      = _p1(Intern, stringify("println"));
  sAdd          = _p1(Intern, stringify("+"));
  sSub          = _p1(Intern, stringify("-"));
  sMul          = _p1(Intern, stringify("*"));

  Obj = _p3(MkClass, _p1(Intern, stringify("Obj")), nil, nil);
    installPrimAsMethod(Obj, sIdentityHash, ObjIdentityHash); 
    installPrimAsMethod(Obj, sPrint,        ObjPrint   );
    installPrimAsMethod(Obj, sPrintln,      ObjPrintln );
    for (int idx = 0; idx < OTSize; idx++) {
      if (IntValue(OT[idx].numSlots) < 0)
        continue;
      OT[idx].cls = Obj;
    }
  Int = _p3(MkClass, _p1(Intern, stringify("Int")), Obj, nil);
    installPrimAsMethod(Obj, sIdentityHash, IntIdentityHash); 
    installPrimAsMethod(Int, sPrint,        IntPrint);
    installPrimAsMethod(Int, sAdd,          IntAdd);
    installPrimAsMethod(Int, sSub,          IntSub);
    installPrimAsMethod(Int, sMul,          IntMul);
  Nil = _p3(MkClass, _p1(Intern, stringify("Nil")), Obj, nil);
    installPrimAsMethod(Nil, sPrint, NilPrint);
    classOf_(nil, Nil);
  Str = _p3(MkClass, _p1(Intern, stringify("Str")), Obj, nil);
    installPrimAsMethod(Str, sPrint, StrPrint);
    for (value_t curr = deref(internedStringsRef); curr != nil; curr = cdr(curr))
      OT[OopValue(car(curr))].cls = Str;

  fp = sp; // done at the end in the code above (intentionally) has left something on the stack
}

int main(int argc, char *argv[]) {
  init(argc > 1);
  value_t ans = send1(sPrintln, _p1(Intern, stringify("Object>>println and send macro worked!"))); printf(" => "); println(ans);
          ans = send1(sPrintln, Int(42));                                                          printf(" => "); println(ans);
          ans = send1(sPrintln, nil);                                                              printf(" => "); println(ans);
          ans = send1(sPrintln, cons(Int(1), Int(2)));                                             printf(" => "); println(ans);
          ans = send2(sSub,     Int(5), Int(6));                                                   printf(" => "); println(ans);
          ans = send1(sPrintln, send1(sIdentityHash, cons(nil, nil)));                             printf(" => "); println(ans);
          ans = send1(sPrintln, send1(sIdentityHash, Int(1234)));                                  printf(" => "); println(ans);
  value_t sX = _p1(Intern, stringify("x"));
  value_t sY = _p1(Intern, stringify("y"));
  _p1(Push, cons(sX, sY));
  value_t Point = _p3(MkClass, _p1(Intern, stringify("Point")), Obj, _p(Pop));
  value_t p     = _p2(MkObj, Point, Int(0));
  send2(sX, p, Int(1234));
  send2(sY, p, Int(4321));
  send1(sPrintln, p);
  send2(sAdd, p, Int(5));
  //_p(PrintOT);
  return 0;
}

