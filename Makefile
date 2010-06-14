CFLAGS = -std=c99 -Wall -ggdb -g3

build : main

go : main
	./main

debug : main
	./main debug

clean :
	rm -f main
