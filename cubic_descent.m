mkc := function(n)
    return EllipticCurve([0, 4*n^2 + 12*n - 3, 0, 32*(n + 3), 0]);
end function;
mkc2 := function(n)
    return EllipticCurve([0, 4*n^2 + 12*n - 3, 0, -128*n - 384, -512*n^3 - 3072*n^2 - 4224*n + 1152]);
end function;
mkc3 := function(n)
    return EllipticCurve([0, 4*n^2 + 12*n - 3, 0, -320*n^2 - 1248*n - 1104, -1024*n^4 - 7168*n^3 - 18944*n^2 - 24576*n - 15040]);
end function;
mkc6 := function(n)
    return EllipticCurve([0, 4*n^2 + 12*n - 3, 0, -640*n^3 - 6080*n^2 - 18528*n - 18384, -2048*n^5 - 39936*n^4 - 281088*n^3 - 935936*n^2 - 1503744*n - 941248]);
end function;

SquarefreePart := function(n)
    if n eq 0 then return 0; end if;
    sign := n lt 0 select -1 else 1;
    n := AbsoluteValue(n);
    f := Factorization(n);
    sqfree := 1;
    for p in f do
        if p[2] mod 2 eq 1 then
            sqfree *:= p[1];
        end if;
    end for;
    return sign * sqfree;
end function;

GetCurve := function(n, iso)
    case iso:
        when 1: return mkc(n);
        when 2: return mkc2(n);
        when 3: return mkc3(n);
        when 6: return mkc6(n);
        else error "Invalid isogenous configuration requested.";
    end case;
end function;

SolveIsogeny2 := function(E_domain, E_codomain, P)
    f2 := DivisionPolynomial(E_domain, 2);
    roots := Roots(f2, RationalField());
    Poly<x> := PolynomialRing(RationalField());
    for r in roots do
        kernel_poly := x - r[1];
        E_cod, phi := IsogenyFromKernel(E_domain, kernel_poly);
        is_iso, iso := IsIsomorphic(E_cod, E_codomain);
        if is_iso then
            P_cod := P @@ iso;
            return DualIsogeny(phi)(P_cod);
        end if;
    end for;
    error "SolveIsogeny2: No matching 2-isogeny found between the curves.";
end function;

SolveIsogeny3 := function(E_domain, E_codomain, P)
    f3 := DivisionPolynomial(E_domain, 3);
    roots := Roots(f3, RationalField());
    Poly<x> := PolynomialRing(RationalField());
    for r in roots do
        kernel_poly := x - r[1];
        E_cod, phi := IsogenyFromKernel(E_domain, kernel_poly);
        is_iso, iso := IsIsomorphic(E_cod, E_codomain);
        if is_iso then
            P_cod := P @@ iso;
            return DualIsogeny(phi)(P_cod);
        end if;
    end for;
    error "SolveIsogeny3: No matching 3-isogeny found between the curves.";
end function;

map2 := function(n, P)
    return SolveIsogeny2(mkc(n), mkc2(n), P);
end function;

map3 := function(n, P)
    return SolveIsogeny3(mkc(n), mkc3(n), P);
end function;

map6 := function(n, P)
    P_mkc2 := SolveIsogeny3(mkc2(n), mkc6(n), P);
    return SolveIsogeny2(mkc(n), mkc2(n), P_mkc2);
end function;

MyTwoDescent := function(E : RemoveGens:=[])
    S2, S2map := TwoSelmerGroup(E : RemoveTorsion, RemoveGens:=RemoveGens);
    S2elts := [s : s in S2 | not IsIdentity(s)];
    TD := [];
    TDmaps := [* *];
    for s in S2elts do 
        C2, C2toE := TwoCover(s @@ S2map : E:=E);
        Append(~TD, C2);
        Append(~TDmaps, C2toE);
    end for;
    n := Ngens(S2);
    inds := [Index(S2elts, S2.i) : i in [1..n]];
    CTmat := ZeroMatrix(GF(2), n, n);
    for i in [1..n], j in [1..i-1] do 
        ii := inds[i];
        jj := inds[j];
        CTij := CasselsTatePairing(TD[ii], TD[jj]);
        CTmat[i,j] := CTij;  
        CTmat[j,i] := CTij;
    end for; 
    printf "The Cassels-Tate pairing on Sel(2,E)/E[2] is\n%o\n", CTmat;
    error if not IsEven(Rank(CTmat)), "CasselsTatePairing failed the parity check";
    kernel := [v : v in Kernel(CTmat) | not IsZero(v)];
    kernel_inds := [Index(S2elts, S2!Eltseq(v)) : v in kernel];
    S2_4 := [S2elts[ii] : ii in kernel_inds];
    TDCT := [TD[ii] : ii in kernel_inds];
    return TDCT;
end function;

ComputeGeneratorTS_worker := function(number, isogenous, reg : NoFullThreeDesc:=true, NoEightDesc:=false, HyperE:=[], descent_no:=0)
    E := GetCurve(number, isogenous);
    if descent_no eq 0 then
        if (isogenous mod 3 eq 0 and reg lt 110) or (isogenous mod 3 ne 0 and reg lt 135) then 
            descent_no := 4;
        elif (not NoEightDesc and isogenous mod 3 eq 0 and reg lt 240) or (NoEightDesc and reg lt 240) then 
            descent_no := 6;
        elif reg lt 540 and not NoEightDesc then
            descent_no := 8;
        else
            descent_no := 12;
        end if;
        printf "Automatically selected descent depth: %o-descent\n", descent_no;
    end if;
    if #HyperE eq 0 then
        HyperE := MyTwoDescent(E);
    end if;
    case descent_no:
        when 4:
            Crvs4 := [];
            if #HyperE eq 0 then
                Crvs4 := FourDescent(E);
            else
                for HE in HyperE do
                    Crv4 := FourDescent(HE : RemoveTorsion := true);
                    Crvs4 := Crvs4 cat Crv4;
                end for;
            end if;
            index := 1;
            Ps := [];
            bound := Max(10^5, Round(10^(reg / 20 + 2)));
            while #Ps eq 0 do
                if index gt #Crvs4 then
                    Crvs4 := [];
                    if #HyperE eq 0 then
                        Crvs4 := FourDescent(E);
                    else
                        for HE in HyperE do
                            Crv4 := FourDescent(HE : RemoveTorsion := true);
                            Crvs4 := Crvs4 cat Crv4;
                        end for;
                    end if;
                    bound := Min(bound * 10, 10^10);
                    index := 1;
                end if;
                Ps := PointsQI(Crvs4[index], bound : OnlyOne := true);
                index := index + 1;
            end while;
            index := index - 1;
            A, mapA := AssociatedEllipticCurve(Crvs4[index] : E := E);
            P := Saturation([mapA(Ps[1])], 1000 : TorsionFree := true)[1];
        when 6:
            if isogenous mod 3 eq 0 then
                Crv3_isog, mapA_isog := ThreeDescent(E);
                Crv3 := [ c : c in Crv3_isog ];
                mapA := [ m : m in mapA_isog ];
            else
                Crv3_isog, mapA_isog, _, _, isog := ThreeIsogenyDescent(E);
                Crv3 := [ c : c in Crv3_isog ];
                mapA := [ m * DualIsogeny(isog) : m in mapA_isog ];
                if #Crv3 eq 0 or not NoFullThreeDesc then
                    Crv3_gen, mapA_gen := ThreeDescent(E);
                    Crv3 := Crv3 cat [ c : c in Crv3_gen ];
                    mapA := mapA cat [ m : m in mapA_gen ];
                end if;
            end if;
            P6 := [];
            index_2 := 1;
            index_3 := 1;
            bound := Max(10^2, Max(Round(10^(reg / 24 + 1)), Round(10^(reg / 20))));
            flag := false;
            while #P6 eq 0 do
                if index_2 gt #HyperE then
                    bound := bound * 10;
                    index_2 := 1;
                    index_3 := 1;
                end if;
                while #P6 eq 0 do
                    if index_3 gt #Crv3 then break; end if;
                    Crv, map6to3 := SixDescent(HyperE[index_2], Crv3[index_3]);
                    P6 := PointSearch(Crv, bound : OnlyOne := true);
                    index_3 := index_3 + 1;
                end while;
                if #P6 eq 0 and index_3 gt #Crv3 then
                    index_2 := index_2 + 1;
                    index_3 := 1;
                end if;
            end while;
            winning_index := index_3 - 1;
            P3_internal := map6to3(Domain(map6to3) ! P6[1]);
            winning_map := mapA[winning_index];
            comps := Components(winning_map);
            if #comps le 1 then
                P := Saturation([winning_map(P3_internal)], 1000 : TorsionFree := true)[1];
            else
                P3_fixed := Domain(comps[1]) ! Eltseq(P3_internal);
                P_intermediate := comps[1](P3_fixed);
                P_intermediate_fixed := Domain(comps[2]) ! Eltseq(P_intermediate);
                PE := comps[2](P_intermediate_fixed);
                P := Saturation([PE], 1000 : TorsionFree := true)[1];
            end if;
        when 8:
            index := 1;
            Crvs4 := [];
            if #HyperE eq 0 then
                Crvs4 := FourDescent(E);
            else
                for HE in HyperE do
                    Crv4 := FourDescent(HE : RemoveTorsion := true);
                    Crvs4 := Crvs4 cat Crv4;
                end for;
            end if;
            Ps := [];
            print "Doing preliminary PointsQI's...\n";
            while #Ps eq 0 do
                if index gt #Crvs4 then break; end if;
                Ps := PointsQI(Crvs4[index], Min(10^8, Max(10^5, Round(10^(reg / 80 + 2)))) : OnlyOne := true);
                index := index + 1;
            end while;
            if #Ps gt 0 then
                A, mapA := AssociatedEllipticCurve(Crvs4[index - 1] : E := E);
                P := Saturation([mapA(Ps[1])], 1000 : TorsionFree := true)[1];
            else
                Crvs8, maps8 := EightDescent(Crvs4[1]);
                for i in [2..#Crvs4] do
                    Crv8, map8 := EightDescent(Crvs4[i]);
                    Crvs8 := Crvs8 cat Crv8;
                    maps8 := maps8 cat map8;
                end for;
                bound := Max(10^2, Round(10^(reg / 30 + 1)));
                index := 1;
                P8 := [];
                while #P8 eq 0 do
                    if index gt #Crvs8 then break; end if;
                    P8 := PointSearch(Crvs8[index], Round(bound^(3/11)) : OnlyOne := true);
                    if #P8 eq 0 then
                        P8 := PointSearch(Crvs8[index], bound : OnlyOne := true);
                    end if;
                    index := index + 1;
                end while;
                if #P8 gt 0 then
                    index := index - 1;
                    P4 := maps8[index](P8[1]);
                    A, mapA := AssociatedEllipticCurve(Codomain(maps8[index]) : E := E);
                    P := Saturation([mapA(P4)], 1000 : TorsionFree := true)[1];
                else
                    return [0];
                end if;
            end if;
        when 12:
            index := 1;
            Crvs4 := [];
            if #HyperE eq 0 then
                Crvs4 := FourDescent(E);
            else
                for HE in HyperE do
                    Crv4 := FourDescent(HE : RemoveTorsion := true);
                    Crvs4 := Crvs4 cat Crv4;
                end for;
            end if;
            Ps := [];
            print "Doing preliminary PointsQI's...\n";
            while #Ps eq 0 do
                if index gt #Crvs4 then break; end if;
                Ps := PointsQI(Crvs4[index], Min(10^8, Max(10^5, Round(10^(reg / 80 + 2)))) : OnlyOne := true);
                index := index + 1;
            end while;
            if #Ps gt 0 then
                A, mapA := AssociatedEllipticCurve(Crvs4[index - 1] : E := E);
                P := Saturation([mapA(Ps[1])], 1000 : TorsionFree := true)[1];
            else
                if isogenous mod 3 eq 0 then
                    Crvs3 := ThreeDescent(E);
                else
                    Crvs3 := ThreeIsogenyDescent(E);
                    if #Crvs3 eq 0 or not NoFullThreeDesc then
                        Crvs3 := Crvs3 cat ThreeDescent(E);
                    end if;
                end if;
                Crvs12 := [];
                maps12 := [];
                for Crv3 in Crvs3 do
                    // avoid computing fiber product of two covers that produce different generators
                    if #PointSearch(Crv3, 10^4) gt 0 then
                        continue;
                    end if;
                    for C4 in Crvs4 do
                        Crv12, map12 := TwelveDescent(Crv3, C4);
                        Crvs12 := Crvs12 cat Crv12;
                        maps12 := maps12 cat map12;
                    end for;
                end for;
                P12 := [];
                index := 1;
                bound := Max(10^2, Round(10^(reg / 60 + 1)));
                while #P12 eq 0 do
                    while #P12 eq 0 and index le #Crvs12 do
                        P12 := PointSearch(Crvs12[index], bound : OnlyOne);
                        index := index + 1;
                    end while;
                    if #P12 gt 0 then
                        break;
                    end if;
                    if index gt #Crvs12 then
                        index := 1;
                    end if;
                    bound := bound * 10;
                end while;
                index := index - 1;
                P4 := maps12[index](P12[1]);
                A, mapA := AssociatedEllipticCurve(Codomain(maps12[index]) : E := E);
                P := Saturation([mapA(P4)], 1000 : TorsionFree := true)[1];
            end if;
    end case;
    if isogenous eq 1 then
        P_orig := P;
    elif isogenous eq 2 then
        P_orig := map2(number, P);
    elif isogenous eq 3 then
        P_orig := map3(number, P);
    elif isogenous eq 6 then
        P_orig := map6(number, P);
    end if;
    E_orig := mkc(number);
    P_final := Saturation([E_orig ! P_orig], 1000 : TorsionFree := true)[1];
    print "-----------------------------------------";
    print "Verification status:", P_final in E_orig;
    print "True Canonical Height on E_", number, ":", CanonicalHeight(P_final);
    print "-----------------------------------------";
    return Eltseq(P_final)[1..2];
end function;
ComputeGeneratorTS := function(number, isogenous, reg : NoFullThreeDesc:=true, NoEightDesc:=false, HyperE:=[], descent_no:=0)
    P := ComputeGeneratorTS_worker(number, isogenous, reg : NoFullThreeDesc:=NoFullThreeDesc, NoEightDesc:=NoEightDesc, HyperE:=HyperE, descent_no:=descent_no);
    if P eq [0] then
        P := ComputeGeneratorTS_worker(number, isogenous, reg : NoFullThreeDesc:=NoFullThreeDesc, NoEightDesc:=true, HyperE:=HyperE, descent_no:=descent_no);
    end if;
    return P;
end function;
TSSize := function(E)
    HyperE := TwoDescent(E : RemoveTorsion := true);
    TS_order := (#HyperE + 1) / 2;
    return TS_order;
end function;

function BSDEasyTermsQ(E : Precision := 6)
    p_prec := Max(Precision, 20);
    dsc := Integers()!Discriminant(E);
    c_inf := (dsc gt 0) select 2 else 1;
    omegas := c_inf * RealPeriod(E : Precision := p_prec);
    loc := LocalInformation(E);
    tam := &*[ Integers() | l[4] : l in loc ];
    om := &*[ Rationals() | l[1]^((Valuation(dsc, l[1]) - l[2]) div 12) : l in loc ];
    tors := #TorsionSubgroup(E);
    return (tam * om * omegas) / (tors^2);
end function;

ComputeGenerator := function(number, isogenous, descent_no : NoFullThreeDesc:=true, NoEightDesc:=false, MaxReg:=0)
    if RootNumber(mkc(number)) eq 1 then
        error "Rank of curve must be 1";
    end if;
    if isogenous eq 0 then
        reg1 := 1 / BSDEasyTermsQ(mkc(number)) / TSSize(mkc(number));
        reg6 := 1 / BSDEasyTermsQ(mkc6(number)) / TSSize(mkc6(number));
        ratio := reg1 / reg6;
        frac := BestApproximation(RealField(10)!ratio, 100);
        printf "Ratio = %o\n", ratio;
        isogenous := SquarefreePart(Numerator(frac));
        printf "Automatically determined isogenous target curve index: %o\n", isogenous;
        if isogenous eq 1 then
            reg := reg1;
        elif isogenous eq 6 then
            reg := reg6;
        end if;
    end if;
    if isogenous eq 1 then
        E := mkc(number);
    elif isogenous eq 2 then
        E := mkc2(number);
    elif isogenous eq 3 then
        E := mkc3(number);
    elif isogenous eq 6 then
        E := mkc6(number);
    else
        error "Invalid isogenous configuration requested.";
    end if;
    Crv4 := FourDescent(E);
    for C4 in Crv4 do
        P4 := PointsQI(C4, 10^7 : OnlyOne);
        if #P4 gt 0 then
            A, mapA := AssociatedEllipticCurve(C4 : E := E);
            P := Saturation([mapA(P4[1])], 1000 : TorsionFree := true)[1];
            if isogenous eq 1 then
                P_orig := P;
            elif isogenous eq 2 then
                P_orig := map2(number, P);
            elif isogenous eq 3 then
                P_orig := map3(number, P);
            elif isogenous eq 6 then
                P_orig := map6(number, P);
            end if;
            E_orig := mkc(number);
            P_final := Saturation([E_orig ! P_orig], 1000 : TorsionFree := true)[1];
            print "-----------------------------------------";
            print "Verification status:", P_final in E_orig;
            print "True Canonical Height on E_", number, ":", CanonicalHeight(P_final);
            print "-----------------------------------------";
            return Eltseq(P_final)[1..2];
        end if;
    end for;
    rnk, lead := AnalyticRank(mkc(number) : Precision := 6);
    if rnk gt 1 then
        error "Rank of curve must be 1";
    end if;
    reg := lead / BSDEasyTermsQ(E) / TSSize(E);
    printf "Regulator is %o based on BSD formula\n", reg;
    if MaxReg ne 0 and reg gt MaxReg then
        printf "Regulator too large; aborting\n";
        return [];
    end if;
    if descent_no eq 0 then
        if (isogenous mod 3 eq 0 and reg lt 110) or (isogenous mod 3 ne 0 and reg lt 135) then 
            descent_no := 4;
        elif (not NoEightDesc and isogenous mod 3 eq 0 and reg lt 240) or (NoEightDesc and reg lt 240) then 
            descent_no := 6;
        elif reg lt 540 and not NoEightDesc then
            descent_no := 8;
        else
            descent_no := 12;
        end if;
        printf "Automatically selected descent depth: %o-descent\n", descent_no;
    end if;
    TS_order := TSSize(E);
    printf "Tate-Shafarevich group has order %o\n", TS_order;
    HyperE := MyTwoDescent(E);
    return ComputeGeneratorTS(number, isogenous, reg : NoFullThreeDesc:=NoFullThreeDesc, NoEightDesc:=NoEightDesc, HyperE:=HyperE, descent_no:=descent_no);
end function;

SaturateGeneratorFull := function(number, isogenous, gens)
    if isogenous eq 1 then
        gens_orig := gens;
    elif isogenous eq 2 then
        gens_orig := [map2(number, P) : P in gens];
    elif isogenous eq 3 then
        gens_orig := [map3(number, P) : P in gens];
    elif isogenous eq 6 then
        gens_orig := [map6(number, P) : P in gens];
    end if;
    E_orig := mkc(number);
    gens_orig := Saturation(gens_orig, 1000 : TorsionFree := true);
    print "-----------------------------------------";
    print "Verification status:", [(P in E_orig) : P in gens_orig];
    print "Regulator of E_", number, ":", Determinant(HeightPairingMatrix(gens_orig));
    print "-----------------------------------------";
    return [[Eltseq(P)[1], Eltseq(P)[2]] : P in gens_orig];
end function;

forward ComputeGeneratorFull;

ComputeGeneratorFull := function(number, isogenous, rank : known_gens:=[], NoFullThreeDesc:=true, NoEightDesc:=false)
    if isogenous eq 1 then
        E := mkc(number);
    elif isogenous eq 2 then
        E := mkc2(number);
    elif isogenous eq 3 then
        E := mkc3(number);
    elif isogenous eq 6 then
        E := mkc6(number);
    else
        error "Invalid isogenous configuration requested.";
    end if;
    if isogenous mod 3 eq 0 then
        NoEightDesc:=true;
    end if;
    if #known_gens gt 0 then
        known_gens := [E!P : P in known_gens];
        gens := Saturation(known_gens, 1000 : TorsionFree := true);
    else
        gens := [];
    end if;
    if #gens eq rank then
        return SaturateGeneratorFull(number, isogenous, gens);
    end if;
    HyperE := MyTwoDescent(E : RemoveGens := gens);
    for HE in HyperE do
        Ps := RationalPoints(HE : Bound := 162755);
        if #Ps gt 0 then
            A, mapA := AssociatedEllipticCurve(HE : E := E);
            P := mapA(Ps[1]);
            printf "Found rational point %o\n", Eltseq(P)[1..2];
            Append(~gens, P);
            return ComputeGeneratorFull(number, isogenous, rank : known_gens:=gens, NoFullThreeDesc:=NoFullThreeDesc, NoEightDesc:=NoEightDesc);
        end if;
    end for;
    Crv4 := [];
    lim_4desc := 3;
    if isogenous mod 3 eq 0 then lim_4desc := 1; end if;
    for a in [1..lim_4desc] do // try three times
        HyperE := MyTwoDescent(E : RemoveGens := gens);
        Crv4 := [];
        for HE in HyperE do
            Crv4 := Crv4 cat FourDescent(HE : RemoveTorsion := true, RemoveGensEC := gens);
        end for;
        for C4 in Crv4 do
            Ps := PointsQI(C4, 10^7 : OnlyOne);
            if #Ps gt 0 then
                A, mapA := AssociatedEllipticCurve(C4 : E := E);
                P := mapA(Ps[1]);
                printf "Found rational point %o\n", Eltseq(P)[1..2];
                Append(~gens, P);
                return ComputeGeneratorFull(number, isogenous, rank : known_gens:=gens, NoFullThreeDesc:=NoFullThreeDesc, NoEightDesc:=NoEightDesc);
            end if;
        end for;
    end for;
    Crvs4 := [];
    if not NoEightDesc then
        Crvs8, maps8 := EightDescent(Crv4[1]);
        if #Crvs8 gt 0 then
            Crvs4 := [Crv4[1]];
        end if;
        for i in [2..#Crv4] do
            Crv8, map8 := EightDescent(Crv4[i]);
            Crvs8 := Crvs8 cat Crv8;
            maps8 := maps8 cat map8;
            if #Crv8 gt 0 then
                Append(~Crvs4, Crv4[i]);
            end if;
        end for;
        P8 := [];
        for bound in [10^11, 10^15] do
            index := 1;
            while #P8 eq 0 do
                if index gt #Crvs8 then break; end if;
                P8 := PointSearch(Crvs8[index], bound : OnlyOne := true);
                index := index + 1;
            end while;
            if #P8 gt 0 then
                index := index - 1;
                P4 := maps8[index](P8[1]);
                A, mapA := AssociatedEllipticCurve(Codomain(maps8[index]) : E := E);
                gens := Saturation(gens cat [mapA(P4)], 1000 : TorsionFree := true);
                return ComputeGeneratorFull(number, isogenous, rank : known_gens:=gens, NoFullThreeDesc:=NoFullThreeDesc, NoEightDesc:=NoEightDesc);
            end if;
        end for;
    else
        Crvs4 := Crv4;
    end if;
    // 4-descent fails to find a point
    Crvs3, maps3 := ThreeDescent(E);
    Crvs6 := [];
    maps6 := [];
    parent_C3 := [];
    index := 1;
    for Crv3 in Crvs3 do
        // avoid computing fiber product of two covers that produce different generators
        if #PointSearch(Crv3, 10^4) gt 0 then
            index := index + 1;
            continue;
        end if;
        for HE in HyperE do
            Crv6, map6 := SixDescent(HE, Crv3);
            Crvs6 := Crvs6 cat [Crv6];
            maps6 := maps6 cat [map6];
            Append(~parent_C3, index);
        end for;
        index := index + 1;
    end for;
    P6 := [];
    index := 1;
    while #P6 eq 0 and index le #Crvs6 do
        P6 := PointSearch(Crvs6[index], 10^8 : OnlyOne); // takes 5 sec each
        index := index + 1;
    end while;
    if #P6 gt 0 then
        index := index - 1;
        P3_internal := maps6[index](P6[1]);
        comps := Components(maps3[parent_C3[index]]);
        if #comps le 1 then
            PE := maps3[parent_C3[index]](P3_internal);
            printf "Found rational point %o\n", Eltseq(PE)[1..2];
            gens := Saturation(gens cat [PE], 1000 : TorsionFree := true);
        else
            P3_fixed := Domain(comps[1]) ! Eltseq(P3_internal);
            P_intermediate := comps[1](P3_fixed);
            P_intermediate_fixed := Domain(comps[2]) ! Eltseq(P_intermediate);
            PE := comps[2](P_intermediate_fixed);
            printf "Found rational point %o\n", Eltseq(PE)[1..2];
            gens := Saturation(gens cat [PE], 1000 : TorsionFree := true);
        end if;
        return ComputeGeneratorFull(number, isogenous, rank : known_gens:=gens, NoFullThreeDesc:=NoFullThreeDesc, NoEightDesc:=NoEightDesc);
    end if;
    Crvs12 := [];
    maps12 := [];
    for Crv3 in Crvs3 do
        // avoid computing fiber product of two covers that produce different generators
        if #PointSearch(Crv3, 10^4) gt 0 then
            continue;
        end if;
        for C4 in Crvs4 do
            Crv12, map12 := TwelveDescent(Crv3, C4);
            Crvs12 := Crvs12 cat Crv12;
            maps12 := maps12 cat map12;
        end for;
    end for;
    P12 := [];
    index := 1;
    for bound in [10^7, 10^13, 10^18, 10^23] do
        while #P12 eq 0 and index le #Crvs12 do
            P12 := PointSearch(Crvs12[index], bound : OnlyOne);
            index := index + 1;
        end while;
        if #P12 gt 0 then
            break;
        end if;
        if index gt #Crvs12 then
            index := 1;
        end if;
    end for;
    index := index - 1;
    P4 := maps12[index](P12[1]);
    A, mapA := AssociatedEllipticCurve(Codomain(maps12[index]) : E := E);
    P := mapA(P4);
    printf "Found rational point %o\n", Eltseq(P)[1..2];
    gens := Saturation(gens cat [P], 1000 : TorsionFree := true);
    return ComputeGeneratorFull(number, isogenous, rank : known_gens:=gens, NoFullThreeDesc:=NoFullThreeDesc, NoEightDesc:=NoEightDesc);
end function;

Check3 := function(number)
    E := mkc3(number);
    return Round(Sqrt(#ThreeDescentByIsogeny(E)));
end function;

CalcRank2 := function(varlist)
    return ComputeGeneratorFull(varlist[1], varlist[2], 2 : known_gens:=[varlist[3]]);
end function;

SetMemoryLimit(2^31);
SetClassGroupBounds("GRH");
SetVerbose("ThreeDescent", 2);
SetVerbose("PointSearch", 2);
SetVerbose("TwelveDescent", 1);
SetVerbose("FourDescent", 1);
SetVerbose("EightDescent", 2);
SetVerbose("Heegner", 1);
SetVerbose("NineDescent", 2);
SetVerbose("QISearch", 1);
SetVerbose("Selmer", 2);
SetVerbose("Conic", 2);
SetColumns(0);
SetDefaultRealField(RealField(1000));
