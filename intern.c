/*
value_t i_stringify(char *s) {
  int size = strlen(s) + 1, idx = 0;
  push(acc);
  value_t r = acc = allocate(size);
  while (1) {
    slotAtPut(acc, Int(idx), Int(*s));
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
    int diff = IntValue(slotAt(s1, Int(idx))) - *s2;
    if (diff != 0)
      return Int(diff);
    if (*s2 == 0)
      return Int(0);
    idx++;
    s2++;
  }
}

value_t i_intern(char *s) {
  value_t is = internedStrings;
  while (is != nil) {
    if (i_stringCmp(slotAt(is, Int(0)), s) == Int(0))
      return is;
    is = slotAt(is, Int(1));
  }
  push(acc);
  acc = allocate(2);
  slotAtPut(acc, Int(0), i_stringify(s));
  slotAtPut(acc, Int(1), internedStrings);
  internedStrings = acc;
  acc = pop();
  return internedStrings;
}
*/

