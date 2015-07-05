HASTE_SOURCES = main.hs P2P.hs

TYPESCRIPT_SOURCES = webrtc.ts support.ts dragOver.ts doConnect.ts jsConnect.ts
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
	-rm *.js
