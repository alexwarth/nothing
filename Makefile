CFLAGS = -std=c99 -Wall -ggdb

build : main

go : main
	./main

clean :
	rm -f main
