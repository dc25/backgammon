HASTE_SOURCES = main.hs

TYPESCRIPT_SOURCES = support.ts dragOver.ts
JAVASCRIPT_FROM_TYPESCRIPT = $(patsubst %.ts,%.js, $(TYPESCRIPT_SOURCES))

default:all

main.js: $(HASTE_SOURCES)
	hastec main.hs

%.js: %.ts
	tsc $< 

all: main.js $(JAVASCRIPT_FROM_TYPESCRIPT)

clean:
	-rm -r main
	-rm *~
	-rm *.hi
	-rm *.o
