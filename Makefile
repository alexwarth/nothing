CFLAGS = -std=c99 -Wall -ggdb

check : main
	./main

clean :
	rm -f main
