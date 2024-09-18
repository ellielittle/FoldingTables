// Is w an element of W_J
// w::Eltseq, J::SeqEnum -> BoolElt
ElementInSubgroup := function(w, J)
    elems := Set(Eltseq(w));
    return elems subset J;
end function;

// Returns all elements of Wfin
// W::GrpFPCox -> SetEnum
CoxeterElements := function(Wfin)
    assert IsFinite(Wfin);
    w := {LongestElement(Wfin)};
    while #w lt #Wfin do
        w := w join BruhatDescendants(w);
    end while;
    return w;
end function;

// The Coxeter Information (datum)
// type::MonStgElt -> Tup (GrpFPCox,GrpFPCox,RootSys,SeqEnum,ModMatFldElt,SeqEnum,GrpFPCoxElt,GrpFPCoxElt)
CoxeterSetup := function(type)
    W := CoxeterGroup(GrpFPCox, type[1] cat "~" cat type[2..#type]);
    Wfin := CoxeterGroup(GrpFPCox, type);

    w0 := &*[W.i : i in Eltseq(LongestElement(Wfin))];

    root_system := RootSystem(ReflectionGroup(type));
    roots := [Transpose(Matrix(r)) : r in Roots(root_system)];
    h := Transpose(Matrix(HighestRoot(root_system)));
    // Add first n roots + negative of highest root
    a := roots[1..#Generators(Wfin)] cat [-h];
    rm := [Transpose(M) : M in ReflectionMatrices(ReflectionGroup(type))];
    rm := rm[1..#Generators(Wfin)] cat [rm[Round(#rm/2)]];

    // Find all entries that do not commute with the affine node
    affine_connected := {j : j in [1..#Generators(Wfin)] | CoxeterMatrix(W)[#Generators(W), j] gt 2};
    generators := {1..#Generators(Wfin)} diff affine_connected;
    // Find reflection element
    subgroup := [w : w in CoxeterElements(Wfin) | ElementInSubgroup(w, generators)];
    w0J := Sort(subgroup, func<v,w|Length(v)-Length(w)>)[#subgroup];
    w0 := LongestElement(Wfin);
    //Convert to an element of the affine group
    refl := &*[W.i : i in Eltseq(w0J * w0)];

    return <W, Wfin, root_system, a, h, rm, w0, refl>;
end function;

//Checks if a positive root is in a set of positive roots posJroots
CheckPositiveRootInParabolic := function(a, posJroots)
    a := Eltseq(a);
    return {x : x in [1..#a] | a[x] ne 0} subset posJroots;
end function;

// The following code builds up the bounding walls

//Remove the ith col and ith row from R
RemColandRow := function(R, i)
    newR := Remove(R, i);
    newR := [Remove(x, i) : x in newR];
    return newR;
end function;

// Remove a set of cols and rows
RemSet := function(R, S)
    newR := R;
    Sort(~S,func<v,w|w-v>);
    for i in S do
        newR := RemColandRow(newR,i);
    end for;
    return newR;
end function;

// Outputs the matrix of the Coxeter group formed by the vertices corresponding to elements of J
JMatrix := function(J, W)
    // Turning J into a sequence and making sure it is in ascending order
    J := [ j : j in J];
    Sort(~J,func<v,w|v-w>);
    nJ := [i : i in [1..#Generators(W)] | not i in J];
    // The Coxeter Matrix of Wfin
    M := CoxeterMatrix(W);
    R := Eltseq(Rows(M));
    R := [Eltseq(r) : r in R];
    R := RemSet(R, nJ);
    JR := Matrix(R);
    return JR;
end function;

GraphJRtDat := function(J, W)
    JR := JMatrix(J,W);
    R := Eltseq(Rows(JR));
    R := [Eltseq(r) : r in R];
    G := CoxeterGraph(JR);
    Sub := Components(G);
    irrecomp := <>;
    irrecompsing := {};
    for x in Sub do
        indx := [Index(i) : i in x];
        Sort(~indx,func<u,v|u-v>);
        nJ := [i : i in [1..#R] | not i in indx];
        if #indx eq 1 then
            irrecompsing := irrecompsing join {<SymmetricMatrix([1]), indx>};
        else
            irrecomp := irrecomp cat <<Matrix(RemSet(R, nJ)), indx>>;
        end if;
    end for;
    return irrecomp, irrecompsing;
end function;

// Checks that the dimensions line up
check := function(hrot)
    ans := true;
    for x in hrot do
        if not #x[1] eq #x[2] then
            ans := false;
        end if;
    end for;
    return ans;
end function;

// Changes set of roots of sub matrix to roots of W
JRootsToRoots := function(J, datum, roots)
    PhiJ := {};
    for i in roots do
        y := [];
        for x in [1..#Generators(datum[2])] do 
            if x in J then
                y := y cat [i[Index(J, x)]];
            else 
                y:= y cat [0];
            end if;
        end for;
        PhiJ := PhiJ join {y};
    end for;
    return PhiJ;
end function;

// The set of highest roots
HighRootSet := function(J,datum)
    if #J eq 0 then 
        return {};
    end if;
    J := [ j : j in J];
    irrecomp, irrecompsing := GraphJRtDat(J, datum[2]);
    rtsys := {<RootDatum(x[1]),x[2]> : x in irrecomp} join {<RootDatum(x[1]),x[2]> : x in irrecompsing};
    hrot := {<Eltseq(HighestRoot(x[1])),x[2]> : x in rtsys};
    if check(hrot) eq false then
        "Error-highest root set";
    end if;
    hrot := {<x[1], J[x[2]]> : x in hrot};
    PhiJ := {};
    for x in hrot do
        PhiJ := PhiJ join JRootsToRoots(x[2], datum, {x[1]});
    end for;
    PhiJ := {Transpose(Matrix([r])) : r in PhiJ};
    return PhiJ;
end function;

// Gives the bounding walls for the corridor (ie simple and highest root of sub diagram coxeter group)
BoundingWalls := function(J, datum)
    a := datum[4];
    a := {a[i] : i in J};
    b := {-x : x in HighRootSet(J,datum)};
    return a join b;
end function;

// The parabolic setup
// J::SeqEnum, datum::Tup -> Tup (SeqEnum,SeqEnum,SeqEnum)
ParabolicSetup := function(J, datum)
    // Transfers elements in Wfin to the corresponding elements in W
    cosetreps := [Eltseq(x) : x in Transversal(datum[2],J)];
    Sort(~cosetreps, func<u,v|#u-#v>);
    reps := [&*[datum[1].i : i in [0] cat Eltseq(rep)] : rep in cosetreps];
    return <J, BoundingWalls(J, datum), reps>;
end function;




