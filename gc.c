#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

// TODO: figure out why fact still doesn't work (I think RET is messing up the stack b/c 1st RET is ok, but 2nd gets invalid ipb)
// TODO: get rid of acc

typedef unsigned char byte_t;
typedef int           value_t;

value_t nil, acc, stack, sp, globals;

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

value_t push(value_t v) {
  slotAtPut(stack, sp, v);
  sp = Int(IntValue(sp) + 1);
  return v;
}

value_t pop(void) {
  assert(sp > Int(0));
  sp = Int(IntValue(sp) - 1);
  value_t r = slotAt(stack, sp);
  slotAtPut(stack, sp, Int(0));
  return r;
}

size_t gc(void) {
  memset(marked, 0, OTSize);
  int numMarked = mark(acc) + mark(globals);
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
  sp  = Int(0);
  acc = nil;
}

void iprint(value_t v, int n) {
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
        iprint(slotAt(v, Int(i)), n + 1);
      }
    printf("]");
  }
  else
    error("print doesn't know how to handle value (%d)\n", v);
}

void print(value_t v) { iprint(v, 1); }

void println(value_t v) {
  print(v);
  printf("\n");
}

enum { IRET, ILD, IADD, ISUB, IMUL, ICALL, IPUSH, IPOP, ISLOTAT, ISLOTATPUT, IJNZ, IHALT };

void printStack(void) {
  printf("contents of stack: \n");
  int spv = IntValue(sp);
  while (spv > 0) {
    spv--;
    printf("  "); println(slotAt(stack, Int(spv)));
  }
  printf("that's it\n\n");
}

value_t fact;

void interp(value_t ipb) {
  value_t ip = Int(0), fp = sp;
  while (1) {
    value_t instr = slotAt(ipb, ip);
    value_t op1, op2;
    if (DEBUG) printf("==> "); println(instr);
    switch (IntValue(slotAt(instr, Int(0)))) {
      case IADD:  if (DEBUG) printf("executing ADD\n");
                  op2 = pop();
                  op1 = pop();
                  acc = push(Int(IntValue(op1) + IntValue(op2)));
                  break;
      case ISUB:  if (DEBUG) printf("executing SUB\n");
                  op2 = pop();
                  op1 = pop();
                  acc = push(Int(IntValue(op1) - IntValue(op2)));
                  break;
      case IMUL:  if (DEBUG) printf("executing MUL\n");
                  op2 = pop();
                  op1 = pop();
                  acc = push(Int(IntValue(op1) * IntValue(op2)));
                  break;
      case IPOP:  if (DEBUG) printf("executing POP\n");
                  acc = pop();
                  break;
      case IPUSH: if (DEBUG) { printf("executing PUSH "); println(slotAt(instr, Int(1))); }
                  op1 = slotAt(instr, Int(1));
                  acc = push(op1);
                  break;
      case ILD:   if (DEBUG) { printf("executing LD "); println(slotAt(instr, Int(1))); }
                  op1 = slotAt(instr, Int(1));
                  acc = push(slotAt(stack, Int(IntValue(fp) - IntValue(op1))));
                  break;
      case ICALL: if (DEBUG) { printf("executing CALL "); print(slotAt(instr, Int(1))); printf(" "); println(slotAt(instr, Int(2))); }
                  push(slotAt(instr, Int(2)));
                  push(ip);
                  push(ipb);
                  fp  = sp;
                  ip  = Int(0);
                  ipb = slotAt(instr, Int(1));
                  break;
      case IRET:  if (DEBUG) printf("executing RET\n");
                  acc = pop();
                  sp  = fp;
                  ipb = pop();
                  ip  = pop();
printf("rrr\n");
assert(isOop(ipb));
                  int n = IntValue(pop());
                  while (n-- > 0) pop();
                  push(acc);
                  break;
      case IJNZ:  if (DEBUG) printf("executing JNZ\n");
                  acc = pop();
                  if (IntValue(acc) != 0)
                    ip = Int(IntValue(ip) + IntValue(slotAt(instr, Int(1))));
                  break;
      case IHALT: printf("executing HALT, acc="); println(acc); exit(0);
      default:    error("unrecognized instruction (opcode = %d)\n", IntValue(slotAt(instr, Int(0))));
    }
    printStack();
    ip = Int(IntValue(ip) + 1);
  }
}

#define PUSH(X)    mk2(Int(IPUSH), Int(X))
#define LD(O)      mk2(Int(ILD),   Int(O))
#define CALL(F, N) mk3(Int(ICALL), F,     Int(N))
#define HALT       mk1(Int(IHALT))
#define RET        mk1(Int(IRET))
#define ADD        mk1(Int(IADD))
#define SUB        mk1(Int(ISUB))
#define MUL        mk1(Int(IMUL))
#define JNZ(O)     mk2(Int(IJNZ),  Int(O))

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
  acc = mk2(Int(4), nil);
  for (int i = 0; i < 100; i++) mk(1);
  acc = mk2(Int(3), acc);
  for (int i = 0; i < 100; i++) mk(1);
  acc = mk2(Int(2), acc);
  for (int i = 0; i < 100; i++) mk(1);
  acc = mk2(Int(1), acc);
  for (int i = 0; i < 100; i++) mk(1);
  println(acc);
  printf("\n\n\n");
  printOT();
*/
  fact = mk(12);
  addGlobal(fact);
  slotAtPut(fact, Int(0),  nil);
  slotAtPut(fact, Int(1),  LD(4));
  slotAtPut(fact, Int(2),  JNZ(2));
  slotAtPut(fact, Int(3),    PUSH(1));
  slotAtPut(fact, Int(4),    RET);
  slotAtPut(fact, Int(5),  LD(4));
  slotAtPut(fact, Int(6),  LD(4));
  slotAtPut(fact, Int(7),  PUSH(1));
  slotAtPut(fact, Int(8),  SUB);
  slotAtPut(fact, Int(9),  CALL(fact, 1));
  slotAtPut(fact, Int(10), MUL);
  slotAtPut(fact, Int(11), RET);

  value_t prog = mk(3);
  addGlobal(prog);
  slotAtPut(prog, Int(0), PUSH(5));
  slotAtPut(prog, Int(1), CALL(fact, 5));
  slotAtPut(prog, Int(2), HALT);

  interp(prog);
  return 0;
}

