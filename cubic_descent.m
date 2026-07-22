// Define the family of curves
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

// Utility function to get the squarefree part of an integer
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

// Helper to solve and apply a 2-isogeny using rational roots
SolveIsogeny2 := function(E_domain, E_codomain, P)
    f2 := DivisionPolynomial(E_domain, 2);
    roots := Roots(f2, RationalField());
    Poly<x> := PolynomialRing(RationalField());
    
    for r in roots do
        kernel_poly := x - r[1];
        // FIXED: Swapped assignment order so E_cod gets the curve and phi gets the map
        E_cod, phi := IsogenyFromKernel(E_domain, kernel_poly);
        is_iso, iso := IsIsomorphic(E_cod, E_codomain);
        if is_iso then
            P_cod := P @@ iso;
            return DualIsogeny(phi)(P_cod);
        end if;
    end for;
    error "SolveIsogeny2: No matching 2-isogeny found between the curves.";
end function;

// Helper to solve and apply a 3-isogeny using rational roots
SolveIsogeny3 := function(E_domain, E_codomain, P)
    f3 := DivisionPolynomial(E_domain, 3);
    roots := Roots(f3, RationalField());
    Poly<x> := PolynomialRing(RationalField());
    
    for r in roots do
        kernel_poly := x - r[1];
        // FIXED: Swapped assignment order so E_cod gets the curve and phi gets the map
        E_cod, phi := IsogenyFromKernel(E_domain, kernel_poly);
        is_iso, iso := IsIsomorphic(E_cod, E_codomain);
        if is_iso then
            P_cod := P @@ iso;
            return DualIsogeny(phi)(P_cod);
        end if;
    end for;
    error "SolveIsogeny3: No matching 3-isogeny found between the curves.";
end function;

// Map definitions matching your pipeline flow
map2 := function(n, P)
    return SolveIsogeny2(mkc(n), mkc2(n), P);
end function;

map3 := function(n, P)
    return SolveIsogeny3(mkc(n), mkc3(n), P);
end function;

map6 := function(n, P)
    // Map from mkc6 to mkc2 via a 3-isogeny, then mkc2 to mkc via a 2-isogeny
    P_mkc2 := SolveIsogeny3(mkc2(n), mkc6(n), P);
    return SolveIsogeny2(mkc(n), mkc2(n), P_mkc2);
end function;

GenerateTwoCover := function(number, E : Check4Desc:=true)
    R<x> := PolynomialRing(Rationals());
    if Check4Desc then
        print "Checking 4-covers";
        System("echo " cat Sprint(Eltseq(E)) cat " | python3 ~/auto2cover.py >2cover_" cat Sprint(number) cat ".txt");
    else
        print "Not checking 4-covers";
        System("echo " cat Sprint(Eltseq(E)) cat " | python3 ~/auto2cover.py 0 >2cover_" cat Sprint(number) cat ".txt");
    end if;
    P_str := Read("2cover_" cat Sprint(number) cat ".txt");
    P_elt := eval P_str;
    System("rm -f 2cover_" cat Sprint(number) cat ".txt");
    if #P_elt eq 0 then
        return [];
    end if;
    HyperEs := [ HyperellipticCurve(HyperE) : HyperE in P_elt ];
    if Check4Desc then
        return HyperEs;
    else
        print "Doing isomorphism check...";
        HyperEs_unique := [];
        for pending in HyperEs do
            is_unique := true;
            for checked in HyperEs_unique do
                if IsIsomorphic(checked, pending) then
                    is_unique := false;
                    break;
                end if;
            end for;
            if is_unique then
                Append(~HyperEs_unique, pending);
            end if;
        end for;
        return HyperEs_unique;
    end if;
end function;

ComputeGeneratorTS := function(number, isogenous, reg : NoFullThreeDesc:=true, HyperE:=[])
    if isogenous eq 1 or isogenous eq 0 then
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
    descent_no := 0;
    if reg lt 144 then
        descent_no := 4;
    else
        descent_no := 12;
    end if;
    printf "Automatically selected descent depth: %o-descent\n", descent_no;
    if #HyperE eq 0 then
        HyperE := GenerateTwoCover(number, E);
    end if;
    Crvs4 := [];
    if #HyperE eq 0 then
        Crvs4 := FourDescent(E);
    else
        for HE in HyperE do
            Crv4 := FourDescent(HE : RemoveTorsion := true);
            Crvs4 := Crvs4 cat Crv4;
        end for;
    end if;
    // Assume Crvs4 is your flat SeqEnum of 4-cover curves (Crv)
    Unique4Covers := [];

    for C in Crvs4 do
        
        // 3. Check if this canonical model matches any curve we've already kept
        is_duplicate := false;
        for existing_model in Unique4Covers do
            // IsIsomorphic checks for an explicit linear change of variables between the models
            if C eq existing_model then
                is_duplicate := true;
                break;
            end if;
        end for;
        
        // 4. If it's brand new, save the minimized representation
        if not is_duplicate then
            Unique4Covers := Unique4Covers cat [C];
        end if;
    end for;

    // 5. Convert your unique models back into standard Curve objects for point hunting
    Crvs4 := [];
    for model in Unique4Covers do
        Append(~Crvs4, Curve(model));
    end for;
    case descent_no:
        when 4:
            index := 1;
            Ps := [];
            bound := Max(10^5, Round(10^(reg / 20 + 2)));
            while #Ps eq 0 do
                if index gt #Crvs4 then
                    bound := Min(bound * 10, 10^10);
                    index := 1;
                end if;
                Ps := PointsQI(Crvs4[index], bound : OnlyOne := true);
                index := index + 1;
            end while;
            index := index - 1;
            A, mapA := AssociatedEllipticCurve(Crvs4[index] : E := E);
            P := Saturation([mapA(Ps[1])], 1000 : TorsionFree := true)[1];
        when 12:
            index := 1;
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
                    Crvs3 := ThreeDescentByIsogeny(E);
                    if not NoFullThreeDesc then
                        SetVerbose("Selmer", 2);
                        Crvs3 := Crvs3 cat ThreeDescent(E);
                        SetVerbose("Selmer", 0);
                    end if;
                else
                    Crvs3 := ThreeIsogenyDescent(E);
                    if #Crvs3 eq 0 or not NoFullThreeDesc then
                        SetVerbose("Selmer", 2);
                        Crvs3 := Crvs3 cat ThreeDescent(E);
                        SetVerbose("Selmer", 0);
                    end if;
                end if;
                P12 := [];
                index_3 := 1;
                index_4 := 1;
                bound := Max(10^2, Round(10^(reg / 60 + 1)));
                while #P12 eq 0 do
                    while #P12 eq 0 do
                        if index_3 gt #Crvs3 then break; end if;
                        Crvs12, maps12 := TwelveDescent(Crvs3[index_3], Crvs4[index_4]);
                        Crv12 := Crvs12[1];
                        map12 := maps12[1];
                        P12 := PointSearch(Crv12, Round(bound^(3/11)) : OnlyOne := true);
                        if #P12 eq 0 then
                            if reg gt 300 and reg lt 600 then
                                P12 := PointSearch(Crv12, bound : OnlyOne := true, Primes := [11, 13]);
                            else
                                P12 := PointSearch(Crv12, bound : OnlyOne := true);
                            end if;
                        end if;
                        if #P12 eq 0 and #Crvs12 ge 2 then
                            Crv12 := Crvs12[2];
                            map12 := maps12[2];
                            P12 := PointSearch(Crv12, Round(bound^(3/11)) : OnlyOne := true);
                            if #P12 eq 0 then
                                if reg gt 360 and reg lt 600 then
                                    P12 := PointSearch(Crv12, bound : OnlyOne := true, Primes := [11, 13]);
                                else
                                    P12 := PointSearch(Crv12, bound : OnlyOne := true);
                                end if;
                            end if;
                        end if;
                        if #P12 eq 0 then
                            index_3 := index_3 + 1;
                        end if;
                    end while;
                    if #P12 eq 0 then
                        index_3 := 1;
                        index_4 := index_4 + 1;
                        if index_4 gt #Crvs4 then
                            bound := bound * 10;
                            index_4 := 1;
                        end if;
                    end if;
                end while;
                P4 := map12(P12[1]);
                A, mapA := AssociatedEllipticCurve(Crvs4[index_4] : E := E);
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
    return P_final;
end function;

TSSize := function(E)
    HyperE := TwoDescent(E : RemoveTorsion := true);
    TS_order := (#HyperE + 1) / 2;
    return TS_order;
end function;

ComputeGenerator := function(number, isogenous, descent_no : NoFullThreeDesc:=true)
    SetMemoryLimit(0);
    SetClassGroupBounds("GRH");
    reg := 0;
    rnk := -1;
    if RootNumber(mkc(number)) eq 1 then
        error "Rank of curve must be 1";
    end if;
    if isogenous eq 0 then
        reg1, rnk := ConjecturalRegulator(mkc(number) : Precision := 6);
        if rnk gt 1 then
            error "Rank of curve must be 1";
        end if;
        reg1 := reg1 / TSSize(mkc(number));
        printf "Regulator of original curve is %o\n", reg1;
        if reg1 lt 120 then
            isogenous := 1;
            reg := reg1;
        else
            reg6 := ConjecturalRegulator(mkc6(number) : Precision := 6) / TSSize(mkc6(number));
            printf "Regulator of 6-isogenous curve is %o\n", reg6;
            if reg6 lt 240 then
                isogenous := 6;
                reg := reg6;
            else
                ratio := reg1 / reg6;
                frac := BestApproximation(RealField(10)!ratio, 100);
                printf "Ratio = %o\n", ratio;
                isogenous := SquarefreePart(Numerator(frac));
                printf "Automatically determined isogenous target curve index: %o\n", isogenous;
                if isogenous eq 1 then
                    reg := reg1;
                elif isogenous eq 6 then
                    reg := reg6;
                else
                    reg := reg1 / Numerator(frac);
                end if;
            end if;
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
    if reg eq 0 or rnk eq -1 then
        reg, rnk := ConjecturalRegulator(E : Precision := 6);
        if rnk gt 1 then
            error "Rank of curve must be 1";
        end if;
        reg := reg / TSSize(E);
    end if;
    printf "Regulator is %o based on BSD formula\n", reg;
    if reg lt 60 then
        print "Automatically selected descent depth: 2-descent";
        System("echo " cat Sprint(Eltseq(E)) cat " | python3 ~/auto2desc.py >2desc_" cat Sprint(number) cat ".txt");
        P_str := Read("2desc_" cat Sprint(number) cat ".txt");
        P_elt := eval P_str;
        System("rm -f 2desc_" cat Sprint(number) cat ".txt");
        if #P_elt gt 0 then
            _, P := P_elt in E;
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
            return P_final;
        end if;
    end if;
    if descent_no eq 0 then
        if (isogenous mod 3 ne 0 and reg lt 162) then 
            descent_no := 4;
        elif reg lt 270 then 
            descent_no := 6;
        else
            descent_no := 12;
        end if;
        printf "Automatically selected descent depth: %o-descent\n", descent_no;
    end if;
    TS_order := TSSize(E);
    printf "Tate-Shafarevich group has order %o\n", TS_order;
    HyperE := GenerateTwoCover(number, E : Check4Desc := (descent_no ne 6));
    if TS_order gt 1 then
        return ComputeGeneratorTS(number, isogenous, reg : NoFullThreeDesc:=NoFullThreeDesc, HyperE:=HyperE);
    end if;
    P := E!0;
    case descent_no:
        when 4:
            Ps := [];
            bound := Max(10^5, Round(10^(reg / 20 + 2)));
            while #Ps eq 0 and bound le 10^10 do
                Crv4 := FourDescent(HyperE[1] : RemoveTorsion := true)[1];
                Ps := PointsQI(Crv4, bound : OnlyOne := true);
                index_4 := 1;
                while #Ps eq 0 and bound le 10^10 do
                    index_4 := index_4 + 1;
                    if index_4 gt #HyperE then
                        break;
                    end if;
                    Crv4 := FourDescent(HyperE[index_4] : RemoveTorsion := true)[1];
                    Ps := PointsQI(Crv4, bound : OnlyOne := true);
                end while;
                if #Ps eq 0 then
                    bound := Min(bound * 10, 10^10);
                    continue;
                else 
                    Ps := Ps[1];
                end if;
                A, mapA := AssociatedEllipticCurve(Crv4 : E := E);
                P := Saturation([mapA(Ps)], 1000 : TorsionFree := true)[1];
                break;
            end while;
        when 6:
            if isogenous mod 3 eq 0 then
                Crv3_isog, mapA_isog := ThreeDescentByIsogeny(E);
                Crv3 := [ c : c in Crv3_isog ];
                mapA := [ m : m in mapA_isog ];
                if not NoFullThreeDesc then
                    SetVerbose("Selmer", 2);
                    Crv3_gen, mapA_gen := ThreeDescent(E);
                    Crv3 := Crv3 cat [ c : c in Crv3_gen ];
                    mapA := mapA cat [ m : m in mapA_gen ];
                    SetVerbose("Selmer", 0);
                end if;
            else
                Crv3_isog, mapA_isog, _, _, isog := ThreeIsogenyDescent(E);
                Crv3 := [ c : c in Crv3_isog ];
                mapA := [ m * DualIsogeny(isog) : m in mapA_isog ];
                if #Crv3 eq 0 or not NoFullThreeDesc then
                    SetVerbose("Selmer", 2);
                    Crv3_gen, mapA_gen := ThreeDescent(E);
                    Crv3 := Crv3 cat [ c : c in Crv3_gen ];
                    mapA := mapA cat [ m : m in mapA_gen ];
                    SetVerbose("Selmer", 0);
                end if;
            end if;
            P6 := [];
            index_2 := 1;
            index_3 := 1;
            bound := Max(10^2, Max(Round(10^(reg / 24 + 1)), Round(10^(reg / 20))));
            flag := false;
            while #P6 eq 0 do
                if index_2 gt #HyperE then
                    error "Exhausted all available covers in SixDescent loop.";
                end if;
                while #P6 eq 0 do
                    if index_3 gt #Crv3 then
                        if flag then
                            index_2 := index_2 + 1;
                            index_3 := 1;
                        end if;
                        SetVerbose("Selmer", 2);
                        Crv3_gen, mapA_gen := ThreeDescent(E);
                        Crv3 := Crv3 cat [ c : c in Crv3_gen ];
                        mapA := mapA cat [ m : m in mapA_gen ];
                        SetVerbose("Selmer", 0);
                        flag := true;
                    end if;
                    Crv, map6to3 := SixDescent(HyperE[index_2], Crv3[index_3]);
                    P6 := PointSearch(Crv, bound : OnlyOne := true);
                    index_3 := index_3 + 1;
                end while;
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
        when 12:
            index := 1;
            Crvs4 := [];
            for HE in HyperE do
                Crv4 := FourDescent(HE : RemoveTorsion := true);
                Crvs4 := Crvs4 cat Crv4;
            end for;
            // Assume Crvs4 is your flat SeqEnum of 4-cover curves (Crv)
            Unique4Covers := [];

            for C in Crvs4 do
                
                // 3. Check if this canonical model matches any curve we've already kept
                is_duplicate := false;
                for existing_model in Unique4Covers do
                    // IsIsomorphic checks for an explicit linear change of variables between the models
                    if C eq existing_model then
                        is_duplicate := true;
                        break;
                    end if;
                end for;
                
                // 4. If it's brand new, save the minimized representation
                if not is_duplicate then
                    Unique4Covers := Unique4Covers cat [C];
                end if;
            end for;

            // 5. Convert your unique models back into standard Curve objects for point hunting
            Crvs4 := [ Curve(model) : model in Unique4Covers ];
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
                    Crvs3 := ThreeDescentByIsogeny(E);
                    if not NoFullThreeDesc then
                        SetVerbose("Selmer", 2);
                        Crvs3 := Crvs3 cat ThreeDescent(E);
                        SetVerbose("Selmer", 0);
                    end if;
                else
                    Crvs3 := ThreeIsogenyDescent(E);
                    if #Crvs3 eq 0 or not NoFullThreeDesc then
                        SetVerbose("Selmer", 2);
                        Crvs3 := Crvs3 cat ThreeDescent(E);
                        SetVerbose("Selmer", 0);
                    end if;
                end if;
                P12 := [];
                index_3 := 1;
                index_4 := 1;
                bound := Max(10^2, Round(10^(reg / 60 + 1)));
                while #P12 eq 0 do
                    while #P12 eq 0 do
                        if index_3 gt #Crvs3 then break; end if;
                        Crvs12, maps12 := TwelveDescent(Crvs3[index_3], Crvs4[index_4]);
                        Crv12 := Crvs12[1];
                        map12 := maps12[1];
                        P12 := PointSearch(Crv12, Round(bound^(3/11)) : OnlyOne := true);
                        if #P12 eq 0 then
                            if reg gt 300 and reg lt 600 then
                                P12 := PointSearch(Crv12, bound : OnlyOne := true, Primes := [11, 13]);
                            else
                                P12 := PointSearch(Crv12, bound : OnlyOne := true);
                            end if;
                        end if;
                        if #P12 eq 0 and #Crvs12 ge 2 then
                            Crv12 := Crvs12[2];
                            map12 := maps12[2];
                            P12 := PointSearch(Crv12, Round(bound^(3/11)) : OnlyOne := true);
                            if #P12 eq 0 then
                                if reg gt 360 and reg lt 600 then
                                    P12 := PointSearch(Crv12, bound : OnlyOne := true, Primes := [11, 13]);
                                else
                                    P12 := PointSearch(Crv12, bound : OnlyOne := true);
                                end if;
                            end if;
                        end if;
                        if #P12 eq 0 then
                            index_3 := index_3 + 1;
                        end if;
                    end while;
                    if #P12 eq 0 then
                        index_3 := 1;
                        index_4 := index_4 + 1;
                        if index_4 gt #Crvs4 then
                            bound := bound * 10;
                            index_4 := 1;
                        end if;
                    end if;
                end while;
                P4 := map12(P12[1]);
                A, mapA := AssociatedEllipticCurve(Crvs4[index_4] : E := E);
                P := Saturation([mapA(P4)], 1000 : TorsionFree := true)[1];
            end if;
    end case;

    // 6. Trace point back to the original curve mkc(number) via Isogeny Maps
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
    // Coerce into the true original Weierstrass environment and execute final saturation
    P_final := Saturation([E_orig ! P_orig], 1000 : TorsionFree := true)[1];

    // 7. Verification execution block
    print "-----------------------------------------";
    print "Verification status:", P_final in E_orig;
    print "True Canonical Height on E_", number, ":", CanonicalHeight(P_final);
    print "-----------------------------------------";

    return P_final;
end function;

SetMemoryLimit(2^30);
SetClassGroupBounds("GRH");
SetVerbose("ThreeDescent", 2);
SetVerbose("PointSearch", 2);
SetVerbose("TwelveDescent", 1);
SetVerbose("FourDescent", 1);
SetVerbose("EightDescent", 3);
SetVerbose("Heegner", 1);
SetVerbose("NineDescent", 2);
SetVerbose("QISearch", 1);
SetColumns(0);
