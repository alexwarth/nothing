CFLAGS = -std=c99 -Wall -ggdb

check : gc
	./gc

clean :
	rm -f gc
