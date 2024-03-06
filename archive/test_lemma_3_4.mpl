restart;

with(CertSatQM):

#printlevel := -1;
#printlevel := 8;

a := 12;
b := 4;
c := 2;
d := 4;
e := 6;

#a := 383/7;
#b := 27;
#c := 23/2;
#d := 82/7;
#e := 143/6;

#a := 1029/38;
#b := 27;
#c := 23/2;
#d := 44;
#e := 101;

g1 := x+a;
g2 := (x+b)*(x+c);
g3 := (x-c)*(x-d);
g4 := -(x-e);

# lemma_3_4(a, b, c, d, e, x)
# Goal compute certificates of 
# g2 in QM(g1*g2*g3*g4)

s0, s1 := lemma_3_4(a, b, c, d, e, x);

lprint(">> s0", s0);
lprint(">> s1", s1);
lprint(evalb(expand(s0 + s1*g1*g2*g3*g4 - g2) = 0));

#SemiAlgebraic([s0 < 0], [x]);
#SemiAlgebraic([s1 < 0], [x]);

#R := PolynomialRing([x]);
#IsEmpty([s0 < 0], R);
#IsEmpty([s1 < 0], R);
