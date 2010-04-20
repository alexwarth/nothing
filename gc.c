#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <assert.h>

#define DEBUG 1

#define callocate(N, T)  ((T *) calloc(N, sizeof(T)))

#define isInteger(X)     ((X) & 1)
#define IntegerValue(X)  ((X) >> 1)
#define Integer(X)       (((X) << 1) | 1)

#define isOop(X)         (((X) & 1) == 0)
#define OopValue(X)      ((X) >> 1)
#define Oop(X)           ((X) << 1)

void error(char *fmt, ...) {
  va_list args;
  va_start(args, fmt);
  fprintf(stderr, "error: ");
  vfprintf(stderr, fmt, args);
  fprintf(stderr, "\n");
}

typedef unsigned char byte_t;
typedef int           value_t;

value_t nil, acc, internedStrings;

typedef struct OTEntry {
  size_t numSlots;
  union {
    value_t        *slots;
    struct OTEntry *next;
  } ptr;
} OTEntry;

size_t OTSize;
OTEntry *OT, *freeList;
byte_t *marked, *isGlobal;

const size_t OrigOTSize = 1;

void growOT(void) {
  size_t  newOTSize    = OTSize > 0 ? OTSize * 2 : OrigOTSize;
  if (DEBUG)
    printf("growOT, new size is %li\n", newOTSize);
  OTEntry *newOT       = callocate(newOTSize, OTEntry);
  byte_t  *newMarked   = callocate(newOTSize, byte_t),
          *newIsGlobal = callocate(newOTSize, byte_t);
  memcpy(newOT,       OT,       sizeof(OTEntry) * OTSize);
  memcpy(newIsGlobal, isGlobal, sizeof(byte_t)  * OTSize);
  for (int i = OTSize; i < newOTSize; i++) {
    newOT[i].numSlots = -1;
    newOT[i].ptr.next = i + 1 < newOTSize ? &newOT[i + 1] : NULL;
    newIsGlobal[i]    = 0;
  }
  if (OTSize > 0) {
    free(OT);
    free(marked);
    free(isGlobal);
  }
  freeList = &newOT[OTSize];
  OTSize   = newOTSize;
  OT       = newOT;
  marked   = newMarked;
  isGlobal = newIsGlobal;
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

value_t IRET, ILD, IADD, ICALL, IPUSH,
        /*ip, fp, */stack, sp;

void push(value_t v) {
  slotAtPut(stack, sp, v);
  sp = Integer(IntegerValue(sp) + 1);
}

value_t pop(void) {
  assert(sp > Integer(0));
  sp = Integer(IntegerValue(sp) - 1);
  value_t r = slotAt(stack, sp);
  slotAtPut(stack, sp, nil);
  return r;
}

size_t gc(void) {
  memset(marked, 0, OTSize);
  int numMarked = mark(nil) + mark(acc) + mark(stack) + mark(internedStrings);
  for (int i = 0; i < OTSize; i++)
    if (isGlobal[i]) {
      numMarked += mark(Oop(i));
    }
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
printf("interned strings is now ");
println(internedStrings);
  return internedStrings;
}

void init(void) {
  OTSize = 0;
  growOT();
  nil             = allocate(0);
  acc             = nil;
  internedStrings = nil;
  stack = allocate(10240);
  sp    = Integer(0);
  IRET  = i_intern("ret");
  ILD   = i_intern("ld");
  IADD  = i_intern("add");
  ICALL = i_intern("call");
  IPUSH = i_intern("push");
}

void interp(void) {
  
}

void makeGlobal(value_t v) {
  isGlobal[OopValue(v)] = 1;
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

value_t ref(value_t val) {
  value_t oop = allocate(1);
  slotAtPut(oop, Integer(0), val);
  return oop;
}

value_t llnode(value_t val, value_t next) {
  value_t oop = allocate(2);
  slotAtPut(oop, Integer(0), val);
  slotAtPut(oop, Integer(1), next);
  return oop;
}

/* Print all contents in the object table. */
void printOT() {
  for (int i = 0; i < OTSize; i++) {
    OTEntry *e = &OT[i];
    printf("%d: ", i);
    if (e->numSlots == -1) {
      printf("free -> %p\n", e->ptr.next);
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
  println(i_intern("hello"));
  println(i_intern("world"));
  println(i_intern("a"));
  println(i_intern("ab"));
  println(i_intern("hello"));
  printOT();
  return 0;
/*
  acc = ref(nil);
  for (int i = 0; i < 100; i++) allocate(1);
  slotAtPut(acc, Integer(0), llnode(Integer(4), slotAt(acc, Integer(0))));
  for (int i = 0; i < 100; i++) allocate(1);
  slotAtPut(acc, Integer(0), llnode(Integer(3), slotAt(acc, Integer(0))));
  for (int i = 0; i < 100; i++) allocate(1);
  slotAtPut(acc, Integer(0), llnode(Integer(2), slotAt(acc, Integer(0))));
  for (int i = 0; i < 100; i++) allocate(1);
  slotAtPut(acc, Integer(0), llnode(Integer(1), slotAt(acc, Integer(0))));
  for (int i = 0; i < 100; i++) allocate(1);
  println(acc);
*/
}

