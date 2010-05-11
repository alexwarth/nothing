CFLAGS = -std=c99 -Wall -ggdb

build : main

go : main
	./main

debug : main
	./main debug

clean :
	rm -f main
