HC=ghc
HCFLAGS= -Wall --make
CMP=cmp

.PHONY:	tests bigtest existtest rectest atsyntest

PTS:	*.hs
	$(HC) $(HCFLAGS) Main.hs -o PTS

tests:	bigtest existtest rectest atsyntest

bigtest:	PTS
	./cppPTS examples/bigtest.pts > out
	$(CMP) out examples/bigtest.out

existtest:	PTS
	./cppPTS examples/existtest.pts > out
	$(CMP) out examples/existtest.out

atsyntest:	PTS
	./cppPTS examples/atsyntest.pts > out
	$(CMP) out examples/atsyntest.out

rectest:	PTS
	./cppPTS examples/rec.pts > out
	$(CMP) out examples/rec.out

clean:
	rm -f PTS *.o *.hi out
