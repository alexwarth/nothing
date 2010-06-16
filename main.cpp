#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

// TODO: syntactic sugar: <- is a low-priority "there's another argument" next, e.g., myArray.at(5) <- 6
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

int debug = 0, initDone = 0;

typedef unsigned char byte_t;
typedef int           value_t;

value_t nil, stack, sp, globals, ipb, ip, fp, internedStringsRef, chars,                 // registers, etc.
        Obj, Nil, Int, Str, Var, Closure, Class,                                         // classes
        sIntern, sIdentityHash, sPrint, sPrintln, sAdd, sSub, sMul;                      // selectors

#define allocate(N, T) ((T *) calloc(N, sizeof(T)))                                      // calloc fills memory w/ 0s, i.e., nils

#define isInt(X)            ((X) & 1)                                                    // integers are tagged (lsb = 1)
#define Int(X)              (((X) << 1) | 1)
#define IntValue(X)         ({ value_t _x = X; if (debug) assert(isInt(_x)); _x >> 1; })

#define isOop(X)            (((X) & 1) == 0)
#define Oop(X)              ((X) << 1)
#define OopValue(X)         ({ value_t _x = X; if (debug) assert(isOop(_x)); _x >> 1; })

typedef struct OTEntry { value_t numSlots, cls;
                         union { value_t *slots;
                                 struct OTEntry *next; } ptr;                               } OTEntry;

typedef struct         { value_t name, slotNames, numSlots, vTableSize, sels, impls, super; } classSlots;

const size_t OrigOTSize = 2; // must be >= 2
size_t OTSize = 0;
OTEntry *OT, *freeList;
byte_t *marked;

void vprintf2(char *fmt, va_list args, value_t n = Int(5));

void  printf2(char *fmt, ...) { va_list args; va_start(args, fmt); vprintf2(fmt, args);                     va_end(args); }
void dPrintf2(char *fmt, ...) { if (!debug) return;
                                va_list args; va_start(args, fmt); vprintf2(fmt, args);                     va_end(args); }
void    error(char *fmt, ...) { va_list args; va_start(args, fmt); printf2("error: "); vprintf2(fmt, args); va_end(args);
                                printf2("\n"); exit(1); }

#define dAssert(cond)        ({ if (debug) assert(cond); })

void growOT(void) {
  size_t  newOTSize    = OTSize > 0 ? OTSize * 2 : OrigOTSize;
  dPrintf2("growOT, new size is %d\n", newOTSize);
  OTEntry *newOT       = allocate(newOTSize, OTEntry);
  byte_t  *newMarked   = allocate(newOTSize, byte_t);
  memcpy(newOT, OT, sizeof(OTEntry) * OTSize);
  for (int i = OTSize; i < newOTSize; i++) {
    newOT[i].numSlots = Int(-1);
    newOT[i].ptr.next = i + 1 < newOTSize ? &newOT[i + 1] : NULL;
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
                                          dAssert(0 <= _idx && _idx < IntValue(OT[_oop].numSlots));       \
                                          OT[_oop].ptr.slots[_idx]; })

#define slotAtPut(oop, idx, val)       ({ value_t _oop = OopValue(oop), _idx = IntValue(idx), _val = val; \
                                          dAssert(0 <= _idx && _idx < IntValue(OT[_oop].numSlots));       \
                                          OT[_oop].ptr.slots[_idx] = _val; })

value_t numSlots(value_t oop)           { dAssert(isOop(oop));
                                          return OT[OopValue(oop)].numSlots; }

value_t *slots(value_t oop)             { dAssert(isOop(oop));
                                          return OT[OopValue(oop)].ptr.slots; }

value_t classOf(value_t x)              { return isInt(x) ? Int : OT[OopValue(x)].cls;        }
value_t classOf_(value_t x, value_t c)  { dAssert(!isInt(x)); return OT[OopValue(x)].cls = c; }

classSlots *asClass(value_t oop)        { dAssert(isOop(oop));
                                          // TODO: replace the following assert with an instanceof (or at least class) check
                                          dAssert(numSlots(oop) == Int(sizeof(classSlots) / sizeof(value_t)));
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
  for (int i = 0; i < IntValue(e.numSlots); i++)
    r += mark(*slot++);
  return r;
}

size_t gc(void) {
  memset(marked, 0, OTSize);
  int numMarked = mark(globals);
  for (int i = 0; i < OTSize; i++) {
    if (marked[i] || OT[i].numSlots == Int(-1))
      continue;
    free(OT[i].ptr.slots);
    OT[i].numSlots = Int(-1);
    OT[i].cls      = nil;
    OT[i].ptr.next = freeList;
    freeList       = &OT[i];
  }
  dPrintf2("GC reclaimed %d OTEntries\n", OTSize - numMarked);
  return OTSize - numMarked;
}

value_t mk(size_t numSlots) {
  if (freeList == NULL || debug) {
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

const size_t MaxNumPrims = 64;
value_t (*prims[MaxNumPrims])(value_t);
void *primNames[MaxNumPrims];
size_t numPrims = 0;

value_t addPrim(char *n, value_t (*f)(value_t)) { assert(numPrims < MaxNumPrims);
                                                  prims[numPrims]     = f;
                                                  primNames[numPrims] = n;
                                                  return Int(numPrims++); }

value_t store(value_t offset, value_t v)        { return slotAtPut(stack, Int(IntValue(fp) - IntValue(offset)), v); }
value_t load (value_t offset)                   { return slotAt   (stack, Int(IntValue(fp) - IntValue(offset)));    }

value_t fsend1(value_t sel, value_t ecv);

void vprintf2(char *fmt, va_list args, value_t n) {
  int oldDebug = debug; debug = 0;
  while (1)
    switch (*fmt) { case 0:   va_end(args); debug = oldDebug; return;
                    case '%': fmt++;
                              switch (*fmt++) { case '%': putchar('%');                                                  break;
                                                case 'o': fsend1(sPrint, va_arg(args, value_t));                         break;
                                                case 'd': printf("%d", va_arg(args, int));                               break;
                                                case 'S': printf2("ipb(ip=%o): [", ip);
                                                          for (int idx = 0; idx < IntValue(numSlots(ipb)); idx++) {
                                                            if (idx > 0) printf2(", ");
                                                            value_t instr = slotAt(ipb, Int(idx)),
                                                                    prim  = slotAt(instr, Int(0)),
                                                                    arg   = slotAt(instr, Int(1));
                                                            if (idx == IntValue(ip)) printf2("<<");
                                                            printf2("%o(%o)", primNames[IntValue(prim)], arg);
                                                            if (idx == IntValue(ip)) printf2(">>");
                                                          }
                                                          printf2("]\nfp: %o\n", fp);
                                                          printf2("/---------------------------------------------\\\n");
                                                          for (int spv = IntValue(sp); spv >= 0; spv--)
                                                            printf2("  %o\n", slotAt(stack, Int(spv)));
                                                          printf2("\\---------------------------------------------/\n"); break;
                                                default:  putchar('%'); fmt--; };
                              break;
                    default:  putchar(*fmt++); }
}

#define Prim(Name, Arg, Body)             value_t p##Name(value_t Arg) { Body; return nil; } \
                                          value_t Name = addPrim(#Name, p##Name);
#define PMeth(Name, Body)                 Prim(Name, recv, Body)

#define _p(Name)                          _p1(Name, nil)
#define _p1(Name, Arg)                    ({ prims[IntValue(Name)](Arg);                                                          })
#define _p2(Name, Arg1, Arg2)             ({ _p1(Push, Arg2); _p1(Name, Arg1);                                                    })
#define _p3(Name, Arg1, Arg2, Arg3)       ({ _p1(Push, Arg3); _p2(Name, Arg1, Arg2);                                              })
#define _p4(Name, Arg1, Arg2, Arg3, Arg4) ({ _p1(Push, Arg4); _p3(Name, Arg1, Arg2, Arg3);                                        })

#define PushArg(x)                        ({ _p1(Push, x); _p1(Box, Int(0));                                                      })
#define PrepSend(sel, recv)               ({ _p(PrepCall); _p1(Push, sel); _p1(Push, recv); _p1(Box, Int(1)); _p1(Box, Int(0));   \
                                                                                                                              fp; })
#define DoSend(n, retFp)                  ({ _p1(Send, Int(n)); interp(ipb, retFp);                                               })

#define send1(sel, recv)                  ({ value_t retFp = PrepSend(sel, recv);                               DoSend(1, retFp); })
#define send2(sel, recv, arg1)            ({ value_t retFp = PrepSend(sel, recv); PushArg(arg1);                DoSend(2, retFp); })
#define send3(sel, recv, arg1, arg2)      ({ value_t retFp = PrepSend(sel, recv); PushArg(arg1); PushArg(arg2); DoSend(3, retFp); })

Prim(Push, v,          { value_t _v = v;
                         slotAtPut(stack, sp, _v);
                         sp = Int(IntValue(sp) + 1);
                         dAssert(sp < numSlots(stack));
                         return _v; })

Prim(Pop, _,           { dAssert(sp > Int(0));
                         sp = Int(IntValue(sp) - 1);
                         value_t r = slotAt(stack, sp);
                         slotAtPut(stack, sp, nil);     // clear the slot to prevent memory leak
                         return r; })

Prim(Eq, _,            { return _p1(Push, Int(IntValue(_p(Pop)) == IntValue(_p(Pop))));                                      })

Prim(Add, _,           { value_t op2 = _p(Pop); return _p1(Push, Int(IntValue(_p(Pop)) + IntValue(op2)));                    })
Prim(Sub, _,           { value_t op2 = _p(Pop); return _p1(Push, Int(IntValue(_p(Pop)) - IntValue(op2)));                    })
Prim(Mul, _,           { value_t op2 = _p(Pop); return _p1(Push, Int(IntValue(_p(Pop)) * IntValue(op2)));                    })

Prim(Box,   offset,    { value_t i = Int(IntValue(sp) - 1 - IntValue(offset)); slotAtPut(stack, i,   ref(slotAt(stack, i))); })
Prim(Unbox, offset,    { value_t i = Int(IntValue(sp) - 1 - IntValue(offset)); slotAtPut(stack, i, deref(slotAt(stack, i))); })

Prim(Ld, offset,       { return _p1(Push, slotAt   (stack, Int(IntValue(fp) - IntValue(offset))));                           })
Prim(St, offset,       { return           slotAtPut(stack, Int(IntValue(fp) - IntValue(offset)), _p(Pop));                   })

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

PMeth(InstMeth,        { value_t sel      = _p(Pop);
                         value_t impl     = _p(Pop);
                         classSlots *_cls = asClass(recv);
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

PMeth(ObjGetSet,       { value_t nArgs = load(Int(1)); // the number of arguments passed to the method, not the primitive
                         value_t idx   = _p(Pop);
                         switch (IntValue(nArgs)) {
                           case 1:  return slotAt   (recv, idx);
                           case 2:  return slotAtPut(recv, idx, deref(load(Int(-2))));
                           default: error("getter/setter called with %o arguments (must be 1 or 2)", nArgs);
                         } })

Prim(DoPrim, n,        { value_t prim = _p(Pop);
                         value_t arg1 = n > Int(0) ? _p(Pop) : nil;
                         return _p1(Push, _p1(prim, arg1)); })

PMeth(InstGetSet,      { value_t name     = _p(Pop);
                         value_t idx      = _p(Pop);
                         classSlots *_cls = asClass(recv);
                                            slotAtPut(_cls->sels,  idx, name);
                         value_t closure  = slotAtPut(_cls->impls, idx, ref(nil));
                         value_t code     = deref_(closure, mk(6));
                         slotAtPut(code, Int(0), cons(Push,   idx));
                         slotAtPut(code, Int(1), cons(Arg,    Int(1)));    // push boxed receiver
                         slotAtPut(code, Int(2), cons(Unbox,  Int(0)));    // unbox the receiver on the stack
                         slotAtPut(code, Int(3), cons(Push,   ObjGetSet)); // push the primitive
                         slotAtPut(code, Int(4), cons(DoPrim, Int(2)));
                         slotAtPut(code, Int(5), cons(Ret,    nil));       // return (DoPrim's result is top of stack)
                       })

PMeth(MkObj,           { value_t nAddlSlots = _p(Pop);
                         value_t obj        = mk((recv == nil ? 0 : IntValue(asClass(recv)->numSlots)) + IntValue(nAddlSlots));
                         classOf_(obj, recv);
                         return obj; })

PMeth(ClassInit,       { classSlots *_cls  = asClass(recv);
                         _cls->name        = _p(Pop);
                         _cls->super       = _p(Pop);
                         _cls->slotNames   = _p(Pop);
                         _cls->numSlots    = Int(IntValue(numSlots(_cls->slotNames)) +
                                                 IntValue(_cls->super == nil ? Int(0) : asClass(_cls->super)->numSlots));
                         _cls->vTableSize  = Int(16);
                         _cls->sels        = mk(IntValue(_cls->vTableSize));
                         _cls->impls       = mk(IntValue(_cls->vTableSize));
                         for (value_t idx = Int(0); idx < numSlots(_cls->slotNames); idx = Int(IntValue(idx) + 1))
                           _p3(InstGetSet, recv, slotAt(_cls->slotNames, idx), idx);
                         return recv; })

Prim(MkClass, name,    { value_t cls       = addGlobal(Class != nil ? _p2(MkObj, Class, Int(0))
                                                                    : mk(sizeof(classSlots) / sizeof(value_t)));
                         value_t super     = _p(Pop);
                         value_t slotNames = _p(Pop);
                         return _p4(ClassInit, cls, name, super, slotNames); })

Prim(Lookup, _,        { // note: the method cache will be implemented in "userland" (where this primitive will be replaced)
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
                         error("%o does not understand \"%o\"", asClass(classOf(recv))->name, sel);
                         return nil; })

Prim(Send, nArgs,      { fp = Int(IntValue(sp) - IntValue(nArgs) - 1);
                         store(Int(1), nArgs);
                         store(Int(4), ip);
                         value_t method = _p(Lookup);
                         ipb = slotAt(method, Int(0)); // get the code out of the closure
                         ip  = Int(-1);
                         return ipb; })

Prim(Jmp, n,           { ip = Int(IntValue(ip) + IntValue(n));    })
Prim(JZ,  n,           { if (IntValue(_p(Pop)) == 0) _p1(Jmp, n); })
Prim(JNZ, n,           { if (IntValue(_p(Pop)) != 0) _p1(Jmp, n); })

Prim(Halt, _,          { })

PMeth(ObjIdentityHash, { return Int(recv); })

PMeth(NilPrint,        { printf("nil");                                           })
PMeth(IntPrint,        { printf("%d", IntValue(recv));                            })
PMeth(StrPrint,        { for (int idx = 0; idx < IntValue(numSlots(recv)); idx++)
                           putchar(IntValue(slotAt(recv, Int(idx))));             })
PMeth(ObjPrint,        { if (classOf(recv) == nil)
                           printf("???[");
                         else
                           printf2("%o[", asClass(classOf(recv))->name);
                         for (int i = 0; i < IntValue(numSlots(recv)); i++) {
                           if (i > 0) printf(", ");
                           fsend1(sPrint, slotAt(recv, Int(i)));
                         }
                         putchar(']');                                            })
PMeth(ObjPrintln,      { fsend1(sPrint, recv); putchar('\n');                     })

Prim(PrintOT,     _,   { for (int i = 0; i < OTSize; i++) {
                           OTEntry *e = &OT[i];
                           printf("%d: ", i);
                           if (IntValue(e->numSlots) == -1) {
                             int next = e->ptr.next - OT;
                             printf("(free, next=%d)\n", next >= 0 ? next : -1);
                           }
                           else {
                             printf2("%o[", asClass(e->cls)->name);
                             for (int n = 0; n < IntValue(e->numSlots); n++) {
                               value_t v = e->ptr.slots[n];
                               if (n > 0) printf(", ");
                               if (isInt(v)) printf("i%d", IntValue(v)); // ints are shown as i123
                               else          printf("r%d", OopValue(v)); // references are shown as r123
                             }
                             printf("]\n");
                           }
                         } })

value_t interp(value_t prog, value_t retFp = Int(-1)) {
  ipb = prog;
  ip  = Int(0);
  while (1) {
    value_t instr = slotAt(ipb, ip), primIdx = IntValue(car(instr)), op = cdr(instr);
    dPrintf2("\n\n%S\nExecuting instruction <<%o %o>>\n", primNames[primIdx], op);
    if (0 <= primIdx && primIdx < numPrims) prims[primIdx](op);
    else                                    error("%d is not a valid primitive\n", primIdx);
    ip = Int(IntValue(ip) + 1);
    dPrintf2("\n%S\n\n\n");
    if (primIdx == IntValue(Halt))
      break;
    else if (primIdx == IntValue(Ret) && fp == retFp) {
      ip = Int(IntValue(ip) - 1); // undo increment of ip
      break;
    }
  }
  return _p(Pop);
}

value_t fsend1(value_t sel, value_t recv) { value_t retFp = PrepSend(sel, recv); return DoSend(1, retFp); }

PMeth(IntAdd,    { return Int(IntValue(recv) + IntValue(deref(_p1(Arg, Int(2))))); })
PMeth(IntSub,    { return Int(IntValue(recv) - IntValue(deref(_p1(Arg, Int(2))))); })
PMeth(IntMul,    { return Int(IntValue(recv) * IntValue(deref(_p1(Arg, Int(2))))); })

PMeth(StrCmp,    { value_t s1 = recv;
                   value_t s2 = _p(Pop);
                   for (int idx = Int(0); 1; idx = Int(IntValue(idx) + 1)) {
                     int c1   = idx < numSlots(s1) ? IntValue(slotAt(s1, idx)) : 0;
                     int c2   = idx < numSlots(s2) ? IntValue(slotAt(s2, idx)) : 0;
                     int diff = c1 - c2;
                     if      (diff != 0) return Int(diff);
                     else if (c1 == 0)   return Int(0);
                   } })

PMeth(StrIntern, { value_t internedStrings = deref(internedStringsRef);
                   for (value_t curr = internedStrings; curr != nil; curr = cdr(curr)) {
                     value_t internedString = car(curr);
                     if (_p2(StrCmp, recv, internedString) == Int(0))
                       return internedString;
                   }
                   _p1(Push, recv); // this Push and the Pop below are needed in case recv is not already on the stack
                   deref_(internedStringsRef, cons(recv, internedStrings));
                   _p(Pop);
                   return recv; })

value_t stringify(char *s) {
  value_t r = _p1(Push, _p2(MkObj, Str, Int(strlen(s))));
  for (int idx = 0; *s != 0; idx++, s++)
    slotAtPut(r, Int(idx), Int(*s));
  _p(Pop);
  return r;
}

void installPrimAsMethod(value_t _class, value_t sel, value_t prim) {
  value_t closure = _p1(Push, ref(nil));
  value_t code    = deref_(closure, mk(5));
  slotAtPut(code, Int(0), cons(Arg,    Int(1))); // push boxed receiver
  slotAtPut(code, Int(1), cons(Unbox,  Int(0))); // unbox the receiver on the stack
  slotAtPut(code, Int(2), cons(Push,   prim));   // push the primitive
  slotAtPut(code, Int(3), cons(DoPrim, Int(1)));
  slotAtPut(code, Int(4), cons(Ret,    nil));    // return (DoPrim's result is top of stack)
  _p1(Push, sel);
  _p1(InstMeth, _class);
}

void init(int _debug) {
  debug   = _debug;
  OTSize  = 0;
  sp      = Int(0);
  ip      = Int(-1);
  growOT();
  nil     = mk(0);   // allocate nil before any other objects so it gets to be 0
  globals = cons(nil, nil);
  stack   = addGlobal(mk(10240));
  internedStringsRef = addGlobal(ref(nil));
  chars = addGlobal(mk(256));

  // "objectify" primNames (they were C strings up to this point)
  for (int p = 0; p < numPrims; p++)
    primNames[p] = (void *)_p1(StrIntern, stringify((char *)primNames[p]));
  
  sIntern       = _p1(StrIntern, stringify("intern"));
  sIdentityHash = _p1(StrIntern, stringify("identityHash"));
  sPrint        = _p1(StrIntern, stringify("print"));
  sPrintln      = _p1(StrIntern, stringify("println"));
  sAdd          = _p1(StrIntern, stringify("+"));
  sSub          = _p1(StrIntern, stringify("-"));
  sMul          = _p1(StrIntern, stringify("*"));

  Obj = _p3(MkClass, _p1(StrIntern, stringify("Obj")), nil, nil);
    installPrimAsMethod(Obj, sIdentityHash, ObjIdentityHash); 
    installPrimAsMethod(Obj, sPrint,        ObjPrint       );
    installPrimAsMethod(Obj, sPrintln,      ObjPrintln     );
    for (int idx = 0; idx < OTSize; idx++) {
      if (IntValue(OT[idx].numSlots) < 0)
        continue;
      OT[idx].cls = Obj;
    }
  value_t classSlotNames = _p1(Push, mk(7));
    slotAtPut(classSlotNames, Int(0), _p1(StrIntern, stringify("name"      )));
    slotAtPut(classSlotNames, Int(1), _p1(StrIntern, stringify("slotNames" )));
    slotAtPut(classSlotNames, Int(2), _p1(StrIntern, stringify("numSlots"  )));
    slotAtPut(classSlotNames, Int(3), _p1(StrIntern, stringify("vTableSize")));
    slotAtPut(classSlotNames, Int(4), _p1(StrIntern, stringify("sels"      )));
    slotAtPut(classSlotNames, Int(5), _p1(StrIntern, stringify("impls"     )));
    slotAtPut(classSlotNames, Int(6), _p1(StrIntern, stringify("super     ")));
    assert(numSlots(classSlotNames) == Int(sizeof(classSlots) / sizeof(value_t))); // sanity check
  Class = addGlobal(_p2(MkObj, Obj, Int(7)));
    _p4(ClassInit, Class, _p1(StrIntern, stringify("Class")), Obj, classSlotNames);
    _p(Pop); // pop classSlotNames
    classOf_(Class, Class);
    classOf_(Obj,   Class);
  Int = _p3(MkClass, _p1(StrIntern, stringify("Int")), Obj, nil);
    installPrimAsMethod(Int, sPrint,        IntPrint);
    installPrimAsMethod(Int, sAdd,          IntAdd  );
    installPrimAsMethod(Int, sSub,          IntSub  );
    installPrimAsMethod(Int, sMul,          IntMul  );
  Nil = _p3(MkClass, _p1(StrIntern, stringify("Nil")), Obj, nil);
    installPrimAsMethod(Nil, sPrint, NilPrint);
    classOf_(nil, Nil);
  Str = _p3(MkClass, _p1(StrIntern, stringify("Str")), Obj, nil);
    installPrimAsMethod(Str, sIntern, StrIntern);
    installPrimAsMethod(Str, sPrint,  StrPrint);
    for (value_t curr = deref(internedStringsRef); curr != nil; curr = cdr(curr)) {
      value_t internedString = car(curr);
      OT[OopValue(internedString)].cls = Str;
    }

  fp = sp; // done at the end in the code above (intentionally) has left something on the stack
  initDone = 1;
}

int main(int argc, char *argv[]) {
  init(argc > 1);
  value_t ans = send1(sPrintln, send1(sIntern, stringify("Object>>println and send macro worked!"))); printf2(" => %o\n", ans);
          ans = send1(sPrintln, Int(42));                                                             printf2(" => %o\n", ans);
          ans = send1(sPrintln, Int(42));                                                             printf2(" => %o\n", ans);
          ans = send1(sPrintln, nil);                                                                 printf2(" => %o\n", ans);
          ans = send1(sPrintln, cons(Int(1), Int(2)));                                                printf2(" => %o\n", ans);
          ans = send1(sPrintln, cons(Int(1), Int(2)));                                                printf2(" => %o\n", ans);
          ans = send2(sSub,     Int(5), Int(6));                                                      printf2(" => %o\n", ans);
          ans = send1(sPrintln, send1(sIdentityHash, cons(nil, nil)));                                printf2(" => %o\n", ans);
          ans = send1(sPrintln, send1(sIdentityHash, Int(1234)));                                     printf2(" => %o\n", ans);
  value_t sX  = send1(sIntern,  stringify("x")),
          sY  = send1(sIntern,  stringify("y"));
  value_t Point = _p3(MkClass, send1(sIntern, stringify("Point")), Obj, cons(sX, sY));
  value_t p     = _p2(MkObj, Point, Int(0));
  send2(sX, p, Int(1234));
  send2(sY, p, Int(4321));
  send1(sPrintln, p);
  send2(sAdd, p, Int(5));
  _p(PrintOT);
  return 0;
}

