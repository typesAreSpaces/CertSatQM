restart;

with(CertSatQM):

printlevel := -1;
#printlevel := 8;

read "nat_gens.mpl";

local i, _i, j, a_0, b_k;
local gen, nat, nat_S, f, _roots;
local qmCert;
local st;

test := proc()
    for i from 4 to 20 by 2 do
        lprint(">> Number of intervals", i/2);

        gen := -mul(y, y in map(_i -> (x-_i), [seq(j, j=1 .. i)]));
        nat := gen_nat_gens([gen], x);
        lprint(">> Basis", nat);

        nat_S := semiAlgebraicIntervals(nat, x);
        arch_poly := getArchimedeanPolynomial (x, nat_S);
        print(">> Archimedean polynomial", arch_poly);
        a_0 := nat_S[1, 1];
        b_k := nat_S[nops(nat_S), 2];

        st := time();
        qmCert := liftPO2QM(arch_poly, nat, a_0, b_k, x);
        #print(">> Result", qmCert);
        print(">> Is correct?", checkCorrectnessQM(qmCert, arch_poly));
        print(">> Time CertSatQM", time() - st);


        #for j from 2 to i/2 - 1 do
        #_roots := solve(nat[j]=0,x);
        #f := (x - a_0)*(x - (_roots[1]))*(x - (_roots[2]));
        #lprint(">> f", f);

        #st := time();
        #qmCert := liftPO2QM(f, nat, a_0, b_k, x);
        #print(">> Time CertSatQM", time() - st);
        ##print(">> Result", qmCert);
        ##print(">> Is correct?", checkCorrectnessQM(qmCert, f));
        #end do;
    end do;
end proc;

test2 := proc()
    f := 16-x^2;
    qmCert := liftPO2QM(f, [x-1, (x-2)*(x-3), -(x-4)], 1, 4, x);
    print(">> Result", qmCert);
    print(">> Is correct?", checkCorrectnessQM(qmCert, f));
end proc;

test();
#test2();
