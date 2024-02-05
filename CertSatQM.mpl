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
export zeroPO, unitPO, updatePONatEntry, addPO, prodPO,  scalarProdPO;

export semiAlgebraicIntervals;
local ord, boundInfo;
local decompositionFromBasis;

local checkMembership;
local lemma_1_5;
local natGens;

local checkSosMultipliers;
local checkCorrectnessPO;

export inductiveCert;

# products of the form (x-a), -(x-b), a \leq b
export case_3_1;

# products of the form (x-a), (x-a)(x-b), a < b
export case_3_2;

# products of the form (x-a)(x-b), (x-b)(x-c), a < b < c
export case_3_3;

local lemma_3_1;
local lemma_3_2;
# products of the form (x-a), (x-b)(x-c), a < b < c
export case_3_4;

# products of the form (x-a)(x-b), (x-c)(x-d), a < b < c
export case_3_5;

export cases;

export zeroQM, unitQM, updateQMNatEntry, addQM, prodQM, scalarProdQM;

export  split_basis_PO, liftPO2QM, checkCorrectnessQM;

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
    local basisPO, _zerosPO, _po, po;
        basisPO := map(
            _index -> expand(mul(elem, elem in map(i -> nat[i], _index))),
            powerset([seq(i, i=1..nops(nat))])
                      );
        _zerosPO := [seq(0, i=1..2^nops(nat))];
        _po := zip(`=`, basisPO, _zerosPO);
        po := table(_po);
        return po;
    end proc;

    unitPO := proc(nat)
    local output := zeroPO(nat);
        output[1] := 1;
        return output;
    end proc;

    updatePONatEntry := proc(po, nat_i, new_element)
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

    scalarProdPO := proc(p, sos, nat, x)
    local i;
    local output := zeroPO(nat);
    local _indices := [indices(p1, 'nolist')];
        for i from 1 to nops(_indices) do
            output[_indices[i]] := sos*p[_indices[i]];
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
    local sep_roots_ords := [], factorable_sos := 1;
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
                factorable_sos :=
                factorable_sos*(x-sep_roots_ords[i, 1, j, 1])^(2*iquo(sep_roots_ords[i, 1, j, 2], 2));
                if modp(sep_roots_ords[i, 1, j, 2], 2) = 1 then
                    simpl_roots[i] := [op(simpl_roots[i]), sep_roots_ords[i, 1, j, 1]];
                end if;
            end do;
            simpl_roots[i] := [simpl_roots[i], sep_roots_ords[i, 2]];
        end do;

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

    checkSosMultipliers := proc(po)
        print(">> Entries of po:");
    local sos_multipliers := [entries(po, 'nolist')];
        map(proc(_p)
                print(SemiAlgebraic([_p < 0], [x]));
            end proc, sos_multipliers);
    end proc;

    checkCorrectnessPO := proc(po, sos_extra, f)
    local basis_element := [indices(po, 'nolist')];
    local sos_multiplier := [entries(po, 'nolist')];
    local i, output := 0;
        for i from 1 to nops(basis_element) do
            output := output + sos_multiplier[i]*basis_element[i];
        end do;

        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Original polynomial: ", expand(f)));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Result: ", expand(sos_extra*output)));

        return expand(sos_extra*output - f);
    end proc;

    # Assumption: SemiAlgebraic(basis) is bounded and non-empty
    inductiveCert := proc(f, basis, x)
        if checkMembership(f, basis, x) = false then
            return 0, 0;
        end if;

    local intervals := semiAlgebraicIntervals(basis, x);
    local nat := natGens(intervals, x);
    local output := unitPO(nat), _temp;
    local todo;

    local factorable_sos, simpl_roots;
        factorable_sos, simpl_roots := decompositionFromBasis(f, intervals, x);

    local i, j, k, size := nops(simpl_roots);
    local a, b, c1, c2, _gamma;

        # Update output using left factors
        a := simpl_roots[1, 2, 2];
        for i from 1 to nops(simpl_roots[1, 1]) do
            c1 := simpl_roots[1, 1, i];
            _temp := zeroPO(nat);
            updatePONatEntry(_temp,     1, a - c1);
            updatePONatEntry(_temp, x - a,      1);
            output := prodPO(output, _temp, nat, x)
        end do;

        # Update output using in between factors
        for i from 2 to size - 1 do
            j := 1;
            todo := simpl_roots[i, 1];
            k := nops(todo);
            a := simpl_roots[i, 2, 1];
            b := simpl_roots[i, 2, 2];
            while j <= k do
                c1 := todo[j];
                c2 := todo[k];
                _gamma := lemma_1_5(c1, c2, a, b);
                DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(SemiAlgebraic([(x-c1)*(x-c2)-_gamma*(x-a)*(x-b) < 0], [x])));

                _temp := zeroPO(nat);
                updatePONatEntry(_temp,           1, (x-c1)*(x-c2) - _gamma*(x-a)*(x-b));
                updatePONatEntry(_temp, (x-a)*(x-b),                             _gamma);
                output := prodPO(output, _temp, nat, x);

                j := j + 1;
                k := k - 1;
            end do;
        end do;

        # Update output using right factors
        b := simpl_roots[size, 2, 1];
        for i from 1 to nops(simpl_roots[size, 1]) do
            c2 := simpl_roots[size, 1, i];
            _temp := zeroPO(nat);
            updatePONatEntry(_temp,        1, c2 - b);
            updatePONatEntry(_temp, -(x - b),      1);
            output := prodPO(output, _temp, nat, x)
        end do;

        #
        # Verify output
        #
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, checkSosMultipliers(output));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Check correctness (difference should be zero):", checkCorrectness(output, factorable_sos, f)));

        return factorable_sos, output;
    end proc;

    case_3_1 := proc(a, b, nat, x)
    local output := zeroQM(nat);
        if a = b then
            updatePONatEntry(output,    x - a, (x-a-1)^2/4);
            updatePONatEntry(output, -(x - a), (x-a+1)^2/4);
        elif a < b then
            updatePONatEntry(output,    x - a, (x-b)^2/(b-a));
            updatePONatEntry(output, -(x - b), (x-a)^2/(b-a));
        else
            return case_3_1(b, a);
        end if;
        return output;
    end proc;

    case_3_2 := proc(a, b, nat, x)
    local output := zeroQM(nat);
        updatePONatEntry(output,       (x-a), (x-b)^2);
        updatePONatEntry(output, (x-a)*(x-b),   (b-a));
        return output;
    end proc;

    case_3_3 := proc(a, b, c, nat, x)
    local output := zeroQM(nat);
    local alpha := (b-a)/(c-b);
        updatePONatEntry(output, (x-a)*(x-b), alpha/(alpha+1)*(x-c)^2);
        updatePONatEntry(output, (x-b)*(x-c),     1/(alpha+1)*(x-a)^2);
        return output;
    end proc;

    # Assume 0 < a < b, 0 < a < c
    lemma_3_1 := proc(a, b, c, x)
        #print(">> Check 1", evalb(0 < a));
        #print(">> Check 2", evalb(a < b));
        #print(">> Check 3", evalb(a < c));
    local p := (x-a)*(x+a)*(x-c)*(x-(a+c)/2)^(2*n);
    local pDeriv := 2*n*(x + a)*(x - a)*(x - c)
        + (x - (a + c)/2)*((x + a)*(x - a) + (x + a)*(x - c) + (x - a)*(x - c));
    local n_curr := 0;
    local min_b, min_a_c, sols;

        while true do
            sols := [RealDomain:-solve(subs({n=n_curr}, pDeriv)=0,x)];
            min_a_c := min(map(x_arg -> subs({n=n_curr,x=evalf(x_arg)}, p), sols));
            min_b := subs({n=n_curr,x=-b}, p);
            if min_b < min_a_c then
                break;
            end if;
            n_curr := n_curr + 1;
        end do;

    local alpha := 1/((b+(a+c)/2)^(2*n_curr)*(b-a)*(b+a)*(b+c));
    local s1 := alpha*(x-(a+c)/2)^(2*n_curr);
    local s0 := (x+b)*(1+s1*(x+a)*(x-a)*(x-c));

        return s0, s1;
    end proc;

    lemma_3_2 := proc(a, b, c, x)
    local alpha, beta, s0, s1;
        if c = b then
            alpha := c^2 - a^2;
            return 1/alpha*(x-a)^2*(x+a)^2, 1/alpha;
        else
            beta := (a^2 - b*c - sqrt((b^2 - a^2)*(c^2 - a^2)))/(b - c);
            alpha := (a + beta)^2*(b - a)*(a+c);
            s1 := 1/alpha*(x - beta)^2;
            s0 := (x+a)*(x-a)*(1 + s1*(x+b)*(x-c));
            #print(">> sign @-a", convert(subs(x=-a, s1*(x+b)*(x-c)), float));
            #print(">> sign @a", convert(subs(x=a, s1*(x+b)*(x-c)), float));
            return s0, s1;
        end if;
    end proc;

    case_3_4 := proc(a, b, c, d, nat, x)
        # Assume b = -c, otherwise
        # x \mapsto x + (b+c)/2;
    local _a := a - (b+c)/2, _b := b - (b+c)/2;
    local _c := c - (b+c)/2, _d := d - (b+c)/2;

        # Compute certificates of g1 in QM(g1 g2 g3)
    local g1__1, g1__g1g2g3;
        g1__1, g1__g1g2g3 := lemma_3_1(_c, -_a, _d, x);

        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of Lemma 3.1 in construction", SemiAlgebraic([g1__1 < 0], [x])));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of Lemma 3.1 in construction", SemiAlgebraic([g1__g1g2g3 < 0], [x])));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of g1 in QM(g1 g2 g3)", expand((x-_a)-(g1__1 + g1__g1g2g3*(x-_a)*(x-_b)*(x-_c)*(-(x-_d))))));

        # Compute certificates of g2 in QM(g1 g2 g3)
    local g2__1, g2__g1g2g3;
        g2__1, g2__g1g2g3 := lemma_3_2(_c, -_a, _d, x);
        #DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Verification of Lemma 3.2 in construction", SemiAlgebraic([g2__1 < 0], [x])));
        #DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, lprint(">> Verification of Lemma 3.2 in construction", SemiAlgebraic([g2__g1g2g3 < 0], [x])));
        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of g2 in QM(g1 g2 g3)", expand((x-_b)*(x+_b)-(g2__1 + g2__g1g2g3*(x-_a)*(x-_b)*(x-_c)*(-(x-_d))))));

    local g1g2__1 := g1__1*g2__1 + g1__g1g2g3*g2__g1g2g3*((x-_a)*(x-_b)*(x-_c)*(-(x-_d)))^2;
    local g1g2__g1g2g3 := g1__1*g2__g1g2g3 + g1__g1g2g3*g2__1;

        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of g1 g2 in QM(g1 g2 g3)", expand((x-_a)*(x-_b)*(x-_c)-(g1g2__1 + g1g2__g1g2g3*(x-_a)*(x-_b)*(x-_c)*(-(x-_d))))));

    local g1g2g3__g1g3 := g2__1;
    local g1g2g3__g2 := g2__g1g2g3*((x-_a)*(x-_d))^2;

        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of g1 g2 g3 in QM(g1, g2, g3)", expand((x-_a)*(x-_b)*(x-_c)*(-(x-_d))-(g1g2g3__g1g3*((x-_a)*(-(x-_d))) + g1g2g3__g2*(x-_b)*(x-_c)))));

    local cert_g1g3 := case_3_1(_a, _d, map(poly -> subs(x=x+(b+c)/2, poly), nat), x);

    local sos_1 := g1g2__1;
    local sos_g1 := g1g2__g1g2g3*g1g2g3__g1g3*cert_g1g3[(x-_a)];
    local sos_g2 := g1g2__g1g2g3*g1g2g3__g2;
    local sos_g3 := g1g2__g1g2g3*g1g2g3__g1g3*cert_g1g3[-(x-_d)];

        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of g1 g2 in QM(g1, g2, g3)", expand((x-_a)*(x-_b)*(x-_c) - (sos_1 + sos_g1*(x-_a) + sos_g2*(x-_b)*(x-_c) + sos_g3*(-(x-_d))))));

    local output := zeroQM(nat);
        #updateQMNatEntry(output, nat_gen, sos_multiplier);
        updateQMNatEntry(output,           1, subs(x=x-(b+c)/2, sos_1));
        updateQMNatEntry(output,       (x-a), subs(x=x-(b+c)/2, sos_g1));
        updateQMNatEntry(output, (x-b)*(x-c), subs(x=x-(b+c)/2, sos_g2));
        updateQMNatEntry(output,      -(x-d), subs(x=x-(b+c)/2, sos_g3));

        DEBUG(__FILE__, __LINE__, ENABLE_DEBUGGING, print(">> Verification of g1 g2 in QM(g1, g2, g3)", expand((x-a)*(x-b)*(x-c) - (output[1] + output[x-a]*(x-a) + output[expand((x-b)*(x-c))]*(x-b)*(x-c) + output[-(x-d)]*(-(x-d))))));
        return output;
    end proc;

    # TODO
    case_3_5 := proc(e, a, b, c, f, nat, x)
    local _e := e - (b+c)/2, _a := a - (b+c)/2;
    local _b := b - (b+c)/2, _c := c - (b+c)/2;
    local _f := f - (b+c)/2;

    local output := zeroQM(nat);
        #updateQMNatEntry(output, nat_gen, sos_multiplier);
        return output;
    end proc;

    # Input:
    # p, q \in nat
    # Output:
    # QMtable of p*q
    cases := proc(p, q, a_0, b_k, nat, x)
    local output := zeroQM(nat);
    local roots_p := sort([solve(p=0,x)]);
    local roots_q := sort([solve(q=0,x)]);
    local num_roots_p := nops(roots_p);
    local num_roots_q := nops(roots_q);
        #print(">> p", p);
        #print(">> q", q);
        #print(">> roots p", roots_p);
        #print(">> roots q", roots_q);

        if num_roots_p = num_roots_q and num_roots_p = 1 then
            if lcoeff(p) = lcoeff(q) then
                updateQMNatEntry(output, 1, p^2);
                return output;
            else
                #print(">> case_3_1 1");
                return case_3_1(roots_p[1], roots_q[1], nat, x);
            end if;
        end if;

        if num_roots_p = 1 and num_roots_q = 2 and roots_q[1] < roots_q[2] then
            if subs(x=roots_p[1], q) = 0 then
                #print(">> case_3_2 2");
                return case_3_2(roots_q[1], roots_q[2], nat, x);
            else
                #print(">> case_3_4 2");
                return case_3_4(roots_p[1], roots_q[1], roots_q[2], b_k, nat, x);
            end if
        end if;

        if num_roots_q = 1 and num_roots_p = 2 and roots_p[1] < roots_p[2] then
            if subs(x=roots_q[1], p) = 0 then
                #print(">> case_3_2 3");
                return case_3_2(roots_p[1], roots_p[2], nat, x);
            else
                #print(">> case_3_4 3");
                return case_3_4(roots_q[1], roots_p[1], roots_p[2], b_k, nat, x);
            end if
        end if;

        if num_roots_p = 2 and num_roots_q = 2 then
            if subs(x=roots_p[2], q) = 0 then
                #print(">> case_3_3 4 1");
                return case_3_3(roots_p[1], roots_p[2], roots_q[2], nat, x);
            end if;
            if subs(x=roots_q[2], p) = 0 then
                #print(">> case_3_3 4 2");
                return case_3_3(roots_q[1], roots_q[2], roots_p[2], nat, x);
            end if;
            if evalb(roots_p[2] < roots_q[1]) then
                #print(">> case_3_5 4 1");
                return case_3_5(a_0, roots_p[1], roots_p[2], roots_q[1], roots_q[2], b_k, nat, x)
            else
                #print(">> case_3_5 4 2");
                return case_3_5(a_0, roots_q[1], roots_q[2], roots_p[1], roots_p[2], b_k, nat, x)
            end if;
        end if;

        return false, false;
    end proc;

    # We implement the vector-like data structure
    # using the `table` data structure
    zeroQM := proc(nat)
    local elem, i;
    local basisQM, _zerosQM, _qm, qm;
        basisQM := [1, op(map(expand, nat))];
        _zerosQM := [seq(0, i=0..nops(nat))];
        _qm := zip(`=`, basisQM, _zerosQM);
        qm := table(_qm);
        return qm;
    end proc;

    unitQM := proc(nat)
    local output := zeroQM(nat);
        output[1] := 1;
        return output;
    end proc;

    updateQMNatEntry := proc(qm, nat_i, new_element)
        qm[expand(nat_i)] := new_element;
        return;
    end proc;

    addQM := proc(q1, q2, nat)
    local i;
    local output := zeroQM(nat);
    local _indices := [indices(q1, 'nolist')];
        for i from 1 to nops(_indices) do
            output[_indices[i]] := q1[_indices[i]] + q2[_indices[i]];
        end do;
        return output;
    end proc;

    # Input:
    # q1, q2 \in QMtable
    # Output:
    # QMtable of p*q
    prodQM := proc(q1, q2, a_0, b_k, nat, x)
    local i, j;
    local output := zeroQM(nat), _temp, todo;
    local _indices := [indices(q1, 'nolist')];
    local size := nops(_indices);
    local _basis, basis_element;
        for i from 1 to size do
            if q1[_indices[i]] = 0 then
                next;
            end if;
            for j from 1 to size do
                if q2[_indices[j]] = 0 then
                    next;
                end if;
                if evalb(_indices[i] = _indices[j]) then
                    output[1] := output[1] + _indices[i]^2*q1[_indices[i]]*q2[_indices[j]];
                else
                    if _indices[i] = 1 then
                        output[_indices[j]] := q2[_indices[j]];
                    elif _indices[j] = 1 then
                        output[_indices[i]] := q1[_indices[i]];
                    else
                        # DEBUG
                        #print(">> i", i);
                        #print(">> j", j);
                        #print(">> indices[i]", _indices[i]);
                        #print(">> indices[j]", _indices[j]);
                        #print(">> q1[indices[i]]", q1[_indices[i]]);
                        #print(">> q2[indices[j]]", q2[_indices[j]]);
                        _temp := cases(_indices[i], _indices[j], a_0, b_k, nat, x);
                        #print(">> _temp @ prodQM", _temp);
                        #print(">> _temp@prodQM", _temp);
                        # Update
                        todo := [indices(_temp, 'nolist')];
                        #print(">> todo@prodQM", todo);
                        for basis_element in todo do
                            #print(">> basis_element", basis_element);
                            #print(">> _temp[basis_element]", _temp[basis_element]);
                            _temp[basis_element] := q1[_indices[i]]*q2[_indices[j]]*_temp[basis_element];
                        end do;
                        output := addQM(output, _temp, nat);
                    end if;
                end if;
            end do;
        end do;
        return output;
    end proc;

    scalarProdQM := proc(p, sos, nat, x)
    local i;
    local output := zeroQM(nat);
    local _indices := [indices(p, 'nolist')];
        for i from 1 to nops(_indices) do
            output[_indices[i]] := sos*p[_indices[i]];
        end do;
        return output;
    end proc;

    split_basis_PO := proc(basis_element, nat);
    local i, elem;
    local todo := map(
        _index -> [expand(mul(elem, elem in map(i -> nat[i], _index))), _index],
        powerset([seq(i, i=1..nops(nat))])
                     );
    local j := 1;
        while true do
            if evalb(expand(todo[j, 1] - basis_element) = 0) then
                return todo[j, 2];
            end if;
            j := j + 1;
        end do;
    end proc;

    liftPO2QM := proc(f, nat, a_0, b_k, x)
        factorable_sos, certPO := inductiveCert(f, nat, x);
    local output := zeroQM(nat), _temp1, _temp2;
        #print(">> factorable_sos", factorable_sos);
        for basis in [indices(certPO, 'nolist')] do
            if evalb(certPO[basis] = 0) = false then
                _temp1 := unitQM(nat);
                for _basis in split_basis_PO(basis, nat) do
                    _temp2 := zeroQM(nat);
                    updateQMNatEntry(_temp2, nat[_basis], 1);
                    _temp1 := prodQM(_temp1, _temp2, a_0, b_k, nat, x);
                end do;
                _temp1 := scalarProdQM(_temp1, certPO[basis], nat, x);
                output := addQM(output, _temp1, nat);
            end if;
        end do;
        if evalb(factorable_sos = 1) = false then
            output := scalarProdQM(output, factorable_sos, nat, x);
        end if;
        return output;
    end proc;

    checkCorrectnessQM := proc(p, f);
        return evalb(0
                     = expand(f
                              - add(y,
                                    y in map(
                                        proc(eq)
                                        local ops := op(eq);
                                            ops[1]*ops[2]
                                        end proc,
                                        [indices(p, 'pairs')]))));
    end proc;
end module;
