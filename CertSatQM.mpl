$define DEBUG(F, L, y, x) if (y) then lprint("Debugging file ", F, " at line ", L); x; end if

with(combinat, powerset);
with(SolveTools, SemiAlgebraic);
with(RegularChains, SemiAlgebraicSetTools, PolynomialRing);
with(SemiAlgebraicSetTools, IsEmpty);
#with(Optimization, Maximize, Minimize);

#_pwd := currentdir();
#currentdir(homedir);
#currentdir("Documents/GithubProjects/RealCertify");

#read "univsos/univsos1.mm";
#read "univsos/univsos2.mm";
#read "univsos/univsos3.mm";

#currentdir(_pwd);

CertSatQM := module() option package;

local Sqf;
export zeroPO, addPO, prodPO;
export updateNatEntry;
local semiAlgebraicIntervals;
local boundInfo, ord;
local decompositionFromBasis;
local checkMembership;
local lemma_1_5;
export inductiveCert;

    Sqf := proc(poly)
    local L, h, f_u, i;
        L := sqrfree(poly);
        h := 1;
        f_u := L[1];
        for i to numelems(L[2]) do
            if type(L[2][i][2], even) then
                h := h*L[2][i][1]^L[2][i][2];
            else
                h := h*L[2][i][1]^(L[2][i][2] - 1);
                f_u := f_u*L[2][i][1];
            end if;
        end do;
# f_u is the strictly positive polynomial
# h is the sums of squares part
        return simplify(f_u), h;
    end proc;

    zeroPO := proc(nat)
    local elem;
    local basisPO, zerosPO, _po, po;
        basisPO := map(
            _index -> simplify(mul(elem, elem in map(i -> nat[i], _index))),
            powerset([seq(i, i=1..nops(nat))])
                      );
        zerosPO := [seq(0, i=1..2^nops(nat))];
        _po := zip(`=`, basisPO, zerosPO);
        po := table(_po);
        return po;
    end proc;

    updateNatEntry := proc(po, nat_i, new_element)
        po[simplify(nat_i)] := new_element;
        return;
    end proc;

# We implement the vector-like data structure
# using the `table` data structure
    addPO := proc(p1, p2, nat)
    local i;
    local output := zeroPO(nat);
    local _indices := [indices(p1, 'nolist')];
        for i from 1 to nops(_indices) do
            output[_indices[i]] := p1[_indices[i]] + p2[_indices[i]];
        end do;
        return output;
    end proc;

# We implement the vector-like data structure
# using the `table` data structure
    prodPO := proc(p1, p2, nat)
    local i, j;
    local output := zeroPO(nat);
    local _indices := [indices(p1, 'nolist')];
    local _sos, _basis;
        for i from 1 to nops(_indices) do
            for j from 1 to nops(_indices) do
                _basis, _sos := Sqf(_indices[i]*_indices[j]);
                output[_basis] := output[_basis] + _sos*p1[_indices[i]]*p2[_indices[j]];
            end do;
        end do;
        return output;
    end proc;


    semiAlgebraicIntervals := proc(basis, x)
        return map
        (bound -> boundInfo(x, bound, 0),
         SemiAlgebraic(map(g -> g >= 0, basis), [x]));
    end proc;

    ord := proc(f, x, _point)
    local g, T;
        g := subs(x = T + _point, f);
        return ldegree(expand(g), T);
    end proc;

    boundInfo := proc(x, bound, eps)
    local i1, i2, j1, j2;
# This is a bounded inequality
        if(nops(bound) = 2) then
            i1 := simplify(op(bound[1])[1]);
            i2 := simplify(op(bound[1])[2]);
            j1 := simplify(op(bound[2])[1]);
            j2 := simplify(op(bound[2])[2]);
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
            i1 := simplify(op(bound[1])[1]);
            j1 := simplify(op(bound[1])[2]);
            if type(bound[1], `=`) then
                if evalb(i1 = x) then
                    return [j1, j1];
                else
                    return [i1, i1];
                end if;
            end if;
            if type(bound[1], `<=`) then
                if evalb(i1 = x) then
                    return [-infinity, j1-eps];
                else
                    return [i1+eps, infinity];
                end if;
            end if;
        end if;
    end proc;

# Assumption:
# - SemiAlgebraic(basis) is bounded and non-empty
# - QM(basis) is saturated
# Output:
# A list of list of the form [X, Y] where:
# - X list with information about the root
# and its multiplicity of f
# i.e., [..., [..., [root_{i, j}, multiplicity_{i, j}], ...], ...]
# where ... < roots_{i-1, n_{i-1}} < roots_{i, 1}
# < ... < roots_{i, n_i} < roots_{i+1, 1} < ...
# - Y contains the intervals which contains the roots in X
    decompositionFromBasis := proc(f, intervals, x)
    local f_roots := [RealDomain:-solve(f = 0, x)];
    local sep_roots_ords := [], factorable_sos := [];
    local first_end_point := intervals[1, 1];
        sep_roots_ords := [
            op(sep_roots_ords),
            [
                select(_root -> _root <= first_end_point, f_roots),
                [-infinity, first_end_point]
            ]
                          ];
    local i, j, num_intervals := nops(intervals);
        for i from 1 to num_intervals - 1 do
            sep_roots_ords :=
            [op(sep_roots_ords),
             [select
              (_root -> intervals[i, 2] <= _root and _root <= intervals[i+1,1],
               f_roots), [intervals[i, 2], intervals[i+1, 1]]]];
        end do;
    local last_end_point := intervals[num_intervals, 2];
        sep_roots_ords := [op(sep_roots_ords),
                           [
                               select(_root -> _root >= last_end_point, f_roots),
                               [last_end_point, infinity]
                           ]
                          ];
        sep_roots_ords := map(l ->
                              [map(_root -> [_root, ord(f, x, _root)], l[1]), l[2]],
                              sep_roots_ords);

    local simpl_roots := [];
    local k := 1;
        for i from 1 to nops(sep_roots_ords) do
            simpl_roots := [op(simpl_roots), []];
            for j from 1 to nops(sep_roots_ords[i, 1]) do
                # sep_roots_ords[i, 1, j, 1] <- root info
                # sep_roots_ords[i, 1, j, 2] <- multiplicity info
                factorable_sos := [
                    op(factorable_sos),
                    (x-sep_roots_ords[i, 1, j, 1])^iquo(sep_roots_ords[i, 1, j, 2], 2)
                                  ];
                if modp(sep_roots_ords[i, 1, j, 2], 2) = 1 then
                    simpl_roots[i] := [op(simpl_roots[i]), sep_roots_ords[i, 1, j, 1]];
                end if;
            end do;
            simpl_roots[i] := [simpl_roots[i], sep_roots_ords[i, 2]];
        end do;

        #map(lprint, sep_roots_ords);

        #return sep_roots_ords;
        return factorable_sos, simpl_roots;
    end proc;

# Assumption: QM(basis) is a saturated quadratic module
    checkMembership := proc(f, basis, x)
    local R := PolynomialRing([x]);
        return IsEmpty([op(map(g -> g >= 0, basis)), f < 0], R);
    end proc;

# Assumption a \leq c_1 \leq c_2 \leq b
# Output: Computes gamma such that
# (x-c_1)(x - c_2) - gamma * (x - a)(x - b) is a sums of squares
    lemma_1_5 := proc(c1, c2, a, b)
        if c1 + c2 > a + b then
            return 2/(b-a)*(b - (c1+c2)/2);
        elif c1 + c2 < a + b then
            return 2/(b-a)*((c1+c2)/2 - a);
        else
            return ((c2-c1)/(b-a))^2;
        end if;
    end proc;

# Assumption: SemiAlgebraic(basis) is bounded and non-empty
    inductiveCert := proc(f, basis, x)

        if checkMembership(f, basis, x) = false then
            return false;
        end if;

    local factorable_sos, simpl_roots, tocombine := [];
    local intervals := semiAlgebraicIntervals(basis, x);

        factorable_sos, simpl_roots := decompositionFromBasis(f, intervals, x);
    local i, size := nops(simpl_roots);
        for i from 2 to size - 1 do
            local todo := simpl_roots[i, 1];
            local a := simpl_roots[i, 2, 1], b := simpl_roots[i, 2, 2];
            local todo_size := nops(todo);
            local j := 1;
            while j <= todo_size do
                local c1 := todo[1];
                local c2 := todo[todo_size];
                local gamma := lemma_1_5(c1, c2, a, b);
                print(">> gamma", gamma);
                print(SemiAlgebraic([(x-c1)*(x-c2)-gamma*(x-a)*(x-b) < 0], [x]));
                j := j + 1;
                todo_size := todo_size - 1;
            end do;
        end do;
        return simpl_roots;
    end proc;
end module;
