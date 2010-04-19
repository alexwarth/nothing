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

value_t nil;

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

size_t gc(void) {
  memset(marked, 0, OTSize);
  int numMarked = mark(nil);
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

void init(void) {
  OTSize = 0;
  growOT();
  nil = allocate(0);
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

int main(void) {
  init();
  value_t acc = ref(nil);
  makeGlobal(acc);
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
}

