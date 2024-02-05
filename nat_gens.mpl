with(SolveTools, SemiAlgebraic);

bound_info1 := proc(x, ineq, eps)
local i1, i2, j1, j2;
    # This is a bounded inequality
    if(nops(ineq) = 2) then
        i1 := simplify(op(ineq[1])[1]);
        i2 := simplify(op(ineq[1])[2]);
        j1 := simplify(op(ineq[2])[1]);
        j2 := simplify(op(ineq[2])[2]);
        if evalb(i1 = x) then
            if evalb(j1 = x) then
                return [min(i2, j2)+eps, max(i2, j2)-eps];
            else
                return [min(i2, j1)+eps, max(i2, j1)-eps];
            end if;
        else
            if evalb(j1 = x) then
                return [min(i1, j2)+eps, max(i1, j2)-eps];
            else
                return [min(i1, j1)+eps, max(i1, j1)-eps];
            end if;
        end if;
        # This is an equality or unbounded inequality
    else
        i1 := simplify(op(ineq[1])[1]);
        j1 := simplify(op(ineq[1])[2]);
        if (type(ineq[1], `=`)) then
            if evalb(i1 = x) then
                return [j1, j1];
            else
                return [i1, i1];
            end if;
        end if;
        if (type(ineq[1], `<=`)) then
            if evalb(i1 = x) then
                return [-infinity, j1-eps];
            else
                return [i1+eps, infinity];
            end if;
        end if;
    end if;
end proc;

gen_nat_gens := proc(basis, x)
local S := SemiAlgebraic(map(f -> f >= 0, basis), [x]);
local intervals := map(ineq -> bound_info1(x, ineq, 0), S);
local size := nops(intervals);
local i;
local out := [];

if size = 0 then 
  return out;
end if;

out := [x - intervals[1][1]];
for i from 1 to size - 1 do
  out := [op(out), (x - intervals[i][2])*(x - intervals[i+1][1])];
end do;
out := [op(out), -(x - intervals[size][2])];

return out;
end proc;
