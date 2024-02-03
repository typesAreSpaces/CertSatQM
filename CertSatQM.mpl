$define ENABLE_DEBUGGING false

$define DEBUG(F, L, y, x) if (y) then lprint("Debugging file ", F, " at line ", L); x; end if

with(combinat, powerset);
with(SolveTools, SemiAlgebraic);
with(RegularChains, SemiAlgebraicSetTools, PolynomialRing);
with(SemiAlgebraicSetTools, IsEmpty);

#_pwd := currentdir();
#currentdir(homedir);
#currentdir("Documents/GithubProjects/RealCertify");

#read "univsos/univsos1.mm";
#read "univsos/univsos2.mm";
#read "univsos/univsos3.mm";

#currentdir(_pwd);

CertSatQM := module() option package;

local sqf;
local auxiliarSosStep;
export zeroPO, unitPO, updateNatEntry, addPO, prodPO;
local semiAlgebraicIntervals;
local ord, boundInfo;
local decompositionFromBasis;
local checkMembership;
local lemma_1_5;
local natGens;
export inductiveCert;

    sqf := proc(poly)
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
        return expand(f_u), h;
    end proc;

    auxiliarSosStep := proc(sos, _basis_element, x)
        if sos = 1 then
            return 1, expand(_basis_element);
        end if;

    local _sos_roots := [solve(sos=0,x)];
    local i, sos_output := 1, basis_element := _basis_element;
    local min_fix := table();
        for i from 1 to nops(_sos_roots) do
            if assigned(min_fix[_sos_roots[i]]) = false then
                min_fix[_sos_roots[i]] := 0;
            end if;
            if subs(x = _sos_roots[i], _basis_element) < 0 and min_fix[_sos_roots[i]] < 2 then
                basis_element := basis_element*(x - _sos_roots[i]);
                min_fix[_sos_roots[i]] := min_fix[_sos_roots[i]] + 1;
            else
                sos_output := sos_output*(x - _sos_roots[i]);
            end if;
        end do;
        return sos_output, expand(basis_element);
    end proc;

    # We implement the vector-like data structure
    # using the `table` data structure
    zeroPO := proc(nat)
    local elem, i;
    local basisPO, zerosPO, _po, po;
        basisPO := map(
            _index -> expand(mul(elem, elem in map(i -> nat[i], _index))),
            powerset([seq(i, i=1..nops(nat))])
                      );
        zerosPO := [seq(0, i=1..2^nops(nat))];
        _po := zip(`=`, basisPO, zerosPO);
        po := table(_po);
        return po;
    end proc;

    unitPO := proc(nat)
    local output := zeroPO(nat);
        output[1] := 1;
        return output;
    end proc;

    updateNatEntry := proc(po, nat_i, new_element)
        po[expand(nat_i)] := new_element;
        return;
    end proc;

    addPO := proc(p1, p2, nat)
    local i;
    local output := zeroPO(nat);
    local _indices := [indices(p1, 'nolist')];
        for i from 1 to nops(_indices) do
            output[_indices[i]] := p1[_indices[i]] + p2[_indices[i]];
        end do;
        return output;
    end proc;

    prodPO := proc(p1, p2, nat, x)
    local i, j;
    local output := zeroPO(nat);
    local _indices := [indices(p1, 'nolist')];
    local size := nops(_indices);
    local _sos, _basis;
        for i from 1 to size do
            for j from 1 to size do
                if evalb(_indices[i] = _indices[j]) then
                    output[1] := output[1] + _indices[i]^2*p1[_indices[i]]*p2[_indices[j]];
                else
                    _basis, _sos := sqf(_indices[i]*_indices[j]);
                    _sos, _basis := auxiliarSosStep(_sos, _basis, x);
                    output[_basis] :=
                    output[_basis] + _sos*p1[_indices[i]]*p2[_indices[j]];
                end if;
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
    # i.e., [..., [..., [root_{}, multiplicity_{i, j}], ...], ...]
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
                # TODO
                # I'm not sure if this should be sorted
                select(_root -> _root <= first_end_point, f_roots),
                [-infinity, first_end_point]
            ]
                          ];
    local i, j, num_intervals := nops(intervals);
        for i from 1 to num_intervals - 1 do
            sep_roots_ords :=
            [op(sep_roots_ords),
             [
                 # TODO
                 # I'm not sure if this should be sorted
                 select
                 (_root ->
                  intervals[i, 2] <= _root and _root <= intervals[i+1,1],
                  f_roots),
                 [intervals[i, 2], intervals[i+1, 1]]
             ]
            ];
        end do;
    local last_end_point := intervals[num_intervals, 2];
        sep_roots_ords := [
            op(sep_roots_ords),
            [
                select(_root ->
                       _root >= last_end_point, f_roots),
                [last_end_point, infinity]
            ]
                          ];
        sep_roots_ords := map(
            l -> [map(_root -> [_root, ord(f, x, _root)], l[1]), l[2]],
            sep_roots_ords
                             );

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

    natGens := proc(intervals, x)
    local i;
    local output := [x-intervals[1, 1]];
        for i from 1 to nops(intervals) - 1 do
            output := [op(output), (x - intervals[i, 2])*(x - intervals[i+1, 1])];
        end do;
        output := [op(output), -(x - intervals[nops(intervals), 2])];
        return output;
    end proc;

    # Assumption: SemiAlgebraic(basis) is bounded and non-empty
    inductiveCert := proc(f, basis, x)
        if checkMembership(f, basis, x) = false then
            return false;
        end if;

    local factorable_sos, simpl_roots, tocombine := [];
    local intervals := semiAlgebraicIntervals(basis, x);
    local nat := natGens(intervals, x);
    local output := unitPO(nat);

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
                local _gamma := lemma_1_5(c1, c2, a, b);
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(SemiAlgebraic([(x-c1)*(x-c2)-gamma*(x-a)*(x-b) < 0], [x])));
                (x-c1)*(x-c2) - _gamma*(x-a)*(x-b);
                j := j + 1;
                todo_size := todo_size - 1;
            end do;
        end do;
        return simpl_roots;
    end proc;
end module;
