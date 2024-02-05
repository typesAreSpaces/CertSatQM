with(CertSatQM):

printlevel := -1;
#printlevel := 8;

read "nat_gens.mpl";

_pwd := currentdir();
currentdir(homedir);
currentdir("Documents/GithubProjects/RealCertify");
read "multivsos/multivsos.mm";

#currentdir(_pwd);

testRealCertify := proc(f, basis)
  local out := multivsos_internal(
      f,
      epsilon=1,
      precSVD=10,
      precSDP=200,
      precOut=30,
      precIn=100,
      gmp=true,
      algo=2,
      glist=basis,
      relaxorder=0,
      denom=false);
  return out;
end proc;

local i, _i, j, a_0, b_k;
local gen, nat, nat_S, f, _roots;
local qmCert;
local st;

for i from 4 to 20 by 2 do
  lprint(">> Number of intervals", i/2);
  gen := -mul(y, y in map(_i -> (x-_i), [seq(j, j=1 .. i)]));
  nat := gen_nat_gens([gen], x);
  lprint(">> Basis", nat);
  nat_S := semiAlgebraicIntervals(nat, x);
  a_0 := nat_S[1, 1];
  b_k := nat_S[nops(nat_S), 2];
  arch_poly := getArchimedeanPolynomial(x, nat_S);
  lprint(">> Archimedean Poly", arch_poly);
  nat_S_ext := [op(nat_S), arch_poly];
  for j from 2 to i/2 - 1 do
    _roots := solve(nat[j]=0,x);
    f := (x - a_0 + 1)*(x - (_roots[1] + (_roots[2]-_roots[1])/3))*(x - (_roots[1]+2*(_roots[2]-_roots[1])/3));
    st := time();
    qmCert := liftPO2QM(f, nat, a_0, b_k, x);
    print(">> Time CertSatQM", time() - st);
    #print(">> Result", qmCert);
    #print(">> Is correct?", checkCorrectnessQM(qmCert, f));
    st := time();
    try
        testRealCertify(f, nat_S);
        print(">> Time RealCertify succeds", time() - st);
    catch:
        print(">> Time RealCertify fails", time() - st);
    end try;
  end do;
end do;

