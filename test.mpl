restart;

with(CertSatQM):

#printlevel := -1;
#printlevel := 5;

e := -3;
a := -2;
b := -1;
c := 1;
d := 2;
f := 3;

g1 := x-e;
g2 := (x-a)*(x-b);
g3 := (x-c)*(x-d);
g4 := -(x-f);

nat := [g1, g2, g3, g4];

output := case_3_5(a, b, c, d, e, f, nat, x);
print(expand(fromQMtoPoly(output)));
print(expand(g2*g3));

#print(checkCorrectnessQM(qmCert, f)); #?
#print(testRealCertify(f, [op(nat), 100-x^2])); #?

#SemiAlgebraic([s0 < 0], [x]);
#SemiAlgebraic([s1 < 0], [x]);
