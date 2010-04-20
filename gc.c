#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

typedef unsigned char byte_t;
typedef int           value_t;

#define DEBUG 1

#define callocate(N, T)  ((T *) calloc(N, sizeof(T)))

#define isInteger(X)     ((X) & 1)
#define Integer(X)       (((X) << 1) | 1)
int IntegerValue(value_t x) { if (DEBUG) assert(isInteger(x)); return x >> 1; }

#define isOop(X)         (((X) & 1) == 0)
#define Oop(X)           ((X) << 1)
int OopValue    (value_t x) { if (DEBUG) assert(isOop(x));     return x >> 1; }

void error(char *fmt, ...) {
  va_list args;
  va_start(args, fmt);
  fprintf(stderr, "error: ");
  vfprintf(stderr, fmt, args);
  fprintf(stderr, "\n");
}

value_t nil, acc/*, internedStrings*/;

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
  if (DEBUG)
    printf("growOT, new size is %li\n", newOTSize);
  OTEntry *newOT       = callocate(newOTSize, OTEntry);
  byte_t  *newMarked   = callocate(newOTSize, byte_t),
          *newIsGlobal = callocate(newOTSize, byte_t);
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

value_t slotAt(value_t oop, value_t idx) {
  assert(isOop(oop));
  assert(isInteger(idx));
  return OT[OopValue(oop)].ptr.slots[IntegerValue(idx)];
}

value_t slotAtPut(value_t oop, value_t idx, value_t val) {
  assert(isOop(oop));
  assert(isInteger(idx));
  return OT[OopValue(oop)].ptr.slots[IntegerValue(idx)] = val;
}

value_t numSlots(value_t oop) {
  assert(isOop(oop));
  return Integer(OT[OopValue(oop)].numSlots);
}

value_t stack, sp;

value_t push(value_t v) {
  slotAtPut(stack, sp, v);
  sp = Integer(IntegerValue(sp) + 1);
  return v;
}

value_t pop(void) {
  assert(sp > Integer(0));
  sp = Integer(IntegerValue(sp) - 1);
  value_t r = slotAt(stack, sp);
  slotAtPut(stack, sp, nil);
  return r;
}

value_t globals;

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
  if (DEBUG)
    printf("GC reclaimed %ld OTEntries\n", OTSize - numMarked);
  return OTSize - numMarked;
}

value_t allocate(size_t numSlots) {
  if (freeList == NULL) {
    gc();
    if (freeList == NULL)
      growOT();
  }
  OTEntry *newGuy = freeList;
  freeList = freeList->ptr.next;
  newGuy->numSlots = numSlots;
  newGuy->ptr.slots = callocate(numSlots, value_t);
  return Oop(newGuy - OT);
}

/*
value_t i_stringify(char *s) {
  int size = strlen(s) + 1, idx = 0;
  push(acc);
  value_t r = acc = allocate(size);
  while (1) {
    slotAtPut(acc, Integer(idx), Integer(*s));
    if (*s == 0)
      break;
    idx++;
    s++;
  }
  acc = pop();
  return r;
}

value_t i_stringCmp(value_t s1, char *s2) {
  int idx = 0;
  while (1) {
    int diff = IntegerValue(slotAt(s1, Integer(idx))) - *s2;
    if (diff != 0)
      return Integer(diff);
    if (*s2 == 0)
      return Integer(0);
    idx++;
    s2++;
  }
}

value_t i_intern(char *s) {
  value_t is = internedStrings;
  while (is != nil) {
    if (i_stringCmp(slotAt(is, Integer(0)), s) == Integer(0))
      return is;
    is = slotAt(is, Integer(1));
  }
  push(acc);
  acc = allocate(2);
  slotAtPut(acc, Integer(0), i_stringify(s));
  slotAtPut(acc, Integer(1), internedStrings);
  internedStrings = acc;
  acc = pop();
  return internedStrings;
}
*/

value_t llnode(value_t val, value_t next) {
  value_t oop = allocate(2);
  slotAtPut(oop, Integer(0), val);
  slotAtPut(oop, Integer(1), next);
  return oop;
}

value_t addGlobal(value_t val) {
  return globals = llnode(val, globals);
}

void init(void) {
  OTSize = 0;
  growOT();
  globals = nil = allocate(0);
  addGlobal(stack = allocate(10240));
  sp  = Integer(0);
  acc = nil;
}

void print(value_t v) {
  if (v == nil)
    printf("nil");
  else if (isInteger(v))
    printf("%d", IntegerValue(v));
  else if (isOop(v)) {
    printf("[");
    for (int i = 0; i < IntegerValue(numSlots(v)); i++) {
      if (i > 0) printf(", ");
      print(slotAt(v, Integer(i)));
    }
    printf("]");
  }
  else
    error("print doesn't know how to handle value (%d)\n", v);
}

void println(value_t v) {
  print(v);
  printf("\n");
}

enum { IRET, ILD, IADD, ISUB, ICALL, IPUSH, IPOP, ISLOTAT, ISLOTATPUT, IHALT };

void printStack(void) {
  printf("contents of stack: \n");
  int spv = IntegerValue(sp);
  while (spv > 0) {
    spv--;
    printf("  "); println(slotAt(stack, Integer(spv)));
  }
  printf("that's it\n\n");
}

void interp(value_t iph) {
  value_t ip = Integer(0), fp = sp;
  while (1) {
    value_t instr = slotAt(iph, ip);
    value_t op1, op2;
    switch (IntegerValue(slotAt(instr, Integer(0)))) {
      case IADD:  if (DEBUG) printf("executing ADD\n");
                  op2 = pop();
                  op1 = pop();
                  acc = push(Integer(IntegerValue(op1) + IntegerValue(op2)));
                  break;
      case ISUB:  if (DEBUG) printf("executing SUB\n");
                  op2 = pop();
                  op1 = pop();
                  acc = push(Integer(IntegerValue(op1) - IntegerValue(op2)));
                  break;
      case IPOP:  if (DEBUG) printf("executing POP\n");
                  acc = pop();
                  break;
      case IPUSH: if (DEBUG) { printf("executing PUSH "); println(slotAt(instr, Integer(1))); }
                  op1 = slotAt(instr, Integer(1));
                  acc = push(op1);
                  break;
      case ILD:   if (DEBUG) { printf("executing LD "); println(slotAt(instr, Integer(1))); }
                  op1 = slotAt(instr, Integer(1));
                  acc = push(slotAt(stack, Integer(IntegerValue(fp) - IntegerValue(op1))));
                  break;
      case ICALL: if (DEBUG) { printf("executing CALL "); print(slotAt(instr, Integer(1))); printf(" "); println(slotAt(instr, Integer(2))); }
                  push(slotAt(instr, Integer(2)));
                  push(ip);
                  push(iph);
                  fp  = sp;
                  ip  = Integer(0);
                  iph = slotAt(instr, Integer(1));
                  break;
      case IRET:  if (DEBUG) printf("executing RET\n");
                  acc = pop();
                  sp  = fp;
                  iph = pop();
                  ip  = pop();
                  int n = IntegerValue(pop());
                  while (n-- > 0) pop();
                  push(acc);
                  break;
      case IHALT: printf("executing HALT, acc="); println(acc); exit(0);
      default:    error("unrecognized instruction (opcode = %d)\n", IntegerValue(slotAt(instr, Integer(0))));
    }
    ip = Integer(IntegerValue(ip) + 1);
  }
}

value_t PUSH(value_t x) {
  value_t r = allocate(2);
  slotAtPut(r, Integer(0), Integer(IPUSH));
  slotAtPut(r, Integer(1), Integer(x));
  return r;
}

value_t LD(value_t offset) {
  value_t r = allocate(2);
  slotAtPut(r, Integer(0), Integer(ILD));
  slotAtPut(r, Integer(1), Integer(offset));
  return r;
}

value_t CALL(value_t func, value_t numArgs) {
  value_t r = allocate(3);
  slotAtPut(r, Integer(0), Integer(ICALL));
  slotAtPut(r, Integer(1), func);
  slotAtPut(r, Integer(2), Integer(numArgs));
  return r;
}

value_t ADD(void) {
  value_t r = allocate(1);
  slotAtPut(r, Integer(0), Integer(IADD));
  return r;
}

value_t HALT(void) {
  value_t r = allocate(1);
  slotAtPut(r, Integer(0), Integer(IHALT));
  return r;
}

value_t RET(void) {
  value_t r = allocate(1);
  slotAtPut(r, Integer(0), Integer(IRET));
  return r;
}


/* Print all contents in the object table. */
void printOT() {
  for (int i = 0; i < OTSize; i++) {
    OTEntry *e = &OT[i];
    printf("%d: ", i);
    if (e->numSlots == -1) {
      int next = e->ptr.next - OT;
      printf("free -> %d\n", next >= 0 ? next : -1);
    } else {
      for (int n = 0; n < e->numSlots; n++) {
        value_t v = e->ptr.slots[n];
        if (isInteger(v)) {
          printf("%d, ", IntegerValue(v)); /* Integers are shown as 123 */
        } else {
          printf("(%d), ", OopValue(v)); /* References are shown as (123) */
        }
      }
      printf("\n");
    }
  }
}

int main(void) {
  init();
/*
  for (int i = 0; i < 100; i++) allocate(1);
  acc = llnode(Integer(4), nil);
  for (int i = 0; i < 100; i++) allocate(1);
  acc = llnode(Integer(3), acc);
  for (int i = 0; i < 100; i++) allocate(1);
  acc = llnode(Integer(2), acc);
  for (int i = 0; i < 100; i++) allocate(1);
  acc = llnode(Integer(1), acc);
  for (int i = 0; i < 100; i++) allocate(1);
  println(acc);
  printf("\n\n\n");
  printOT();
*/
  value_t func = allocate(5);
  addGlobal(func);
  slotAtPut(func, Integer(0), nil);
  slotAtPut(func, Integer(1), LD(5));
  slotAtPut(func, Integer(2), LD(4));
  slotAtPut(func, Integer(3), ADD());
  slotAtPut(func, Integer(4), RET());
  value_t prog = allocate(4);
  addGlobal(prog);
  slotAtPut(prog, Integer(0), PUSH(4));
  slotAtPut(prog, Integer(1), PUSH(3));
  slotAtPut(prog, Integer(2), CALL(func, 2));
  slotAtPut(prog, Integer(3), HALT());
printStack();
  interp(prog);
}

