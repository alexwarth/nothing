CFLAGS = -std=c99 -Wall

check : gc
	./gc

clean :
	rm -f gc
