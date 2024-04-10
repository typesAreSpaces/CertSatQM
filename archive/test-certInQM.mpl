restart;

with(CertSatQM):

check := proc(f, nat, a, b, x)
    qmCert := certInQM(f, nat, a, b, x);
#print(qmCert);
    print(checkCorrectnessQM(qmCert, f));
#print(simplify(fromQMtoPoly(qmCert)));
end proc;

#printlevel := -1;
#printlevel := 5;

nat := [x+6, (x+4)*(x+2), x*(x-2), -(x-4)];
f1 := -x*(x-2)*(x-4);
f2 := -(x+4)*(x+2)*(x-4);
f3 := (x+4)*(x+2)*x*(x-2);
f4 := (x+4)*(x+2)*x*(x-2)*(-(x-4));
f5 := (x+6)*(x+4)*(x+2)*x*(x-2)*(-(x-4));
f6 := (x+6)*(x+4)*(x+2)*x*(x-2)*(-(x-5));

check(f1, nat, -6, 4, x);
check(f2, nat, -6, 4, x);
check(f3, nat, -6, 4, x);
check(f4, nat, -6, 4, x);
check(f5, nat, -6, 4, x);
check(f6, nat, -6, 4, x);
