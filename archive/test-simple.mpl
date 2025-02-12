restart;

with(CertSatQM):

#printlevel := -1;
#printlevel := 8;

read "nat_gens.mpl";

simple_test := proc(f, gens, x)
local a_0, b_k;
local nat, nat_S, _roots;
local qmCert;
local st;

lprint(">> gens ", gens);
lprint(">> f", f);

nat := gen_nat_gens(gens, x);

nat_S := semiAlgebraicIntervals(nat, x);
a_0 := nat_S[1, 1];
b_k := nat_S[nops(nat_S), 2];

arch_poly := getArchimedeanPolynomial(x, nat_S);
nat_ext := [op(nat), arch_poly];

st := time();
qmCert := certInQM(f, nat, a_0, b_k, x);
lprint(">> Time CertSatQM", time() - st);
print(">> Result", qmCert);
#print(">> Is correct?", checkCorrectnessQM(qmCert, f));
end proc;

i := 4;
gens := [-mul(y, y in map(_i -> (x-_i), [seq(j, j=1 .. i)]))];
f := x;
#simple_test(f, gens, x);

#simple_test(x+2, [(x+1)*(x-1), -(x+1)*(x-1)], x);

simple_test(
x+19/100, 
[(x-851/100)*(x-99/10)*(x-249/25), -(x-851/100)*(x-99/10)*(x-249/25)], 
x);
