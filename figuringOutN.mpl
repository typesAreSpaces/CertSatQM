with(Optimization, Minimize);

figuringOut := proc()
    nCurrent := 200;

    p := (x-a)*(x+a)*(x-c)*(x-(a+c)/2)^(2*n);
    pDeriv := 2*n*(x + a)*(x - a)*(x - c) + (x - (a + c)/2)*((x + a)*(x - a) + (x + a)*(x - c) + (x - a)*(x - c));

# Naive approach # Correct answer
    st := time():
    x_sol := minimize(subs({a=1,c=2,n=nCurrent}, p), x=1 .. 2);
    evalf(x_sol); # Correct answer
    time() - st;

# Solve pDeriv with standard solve # Wrong answers, returns complex numbers
#sols2 := [solve(subs({a=1,c=2,n=7}, pDeriv)=0,x)];
#min(map(x_arg -> evalf(subs({a=1,c=2,n=7,x=x_arg}, p)), sols2));

# Solve pDeriv with RealDomain:-solve # The most satisfying solutions
    st := time():
    sols3 := [RealDomain:-solve(subs({a=1,c=2,n=nCurrent}, pDeriv)=0,x)];
#lprint(min(map(x_arg -> subs({a=1,c=2,n=7,x=x_arg}, p), sols3)));
    min(map(x_arg -> subs({a=1,c=2,n=nCurrent,x=evalf(x_arg)}, p), sols3)); #Good solution
    time() - st;
end proc;

#figuringOut();

computeNLemma_3_1 := proc(a, b, c)
local p := (x-a)*(x+a)*(x-c)*(x-(a+c)/2)^(2*n);
local pDeriv := 2*n*(x + a)*(x - a)*(x - c) + (x - (a + c)/2)*((x + a)*(x - a) + (x + a)*(x - c) + (x - a)*(x - c));
local n_curr := 0;
local min_a_c, sols;

    while true do
        sols := [RealDomain:-solve(subs({n = n_curr}, pDeriv)=0,x)];
        min_a_c := min(map(x_arg -> subs({n=n_curr,x=evalf(x_arg)}, p), sols));
        min_b := subs({n=n_curr,x=-b}, p);
        if min_b < min_a_c then
            break;
        end if;
        n_curr := n_curr + 1;
    end do;

    return n_curr;
end proc;

computeNLemma_3_1(1, 10, 300);
