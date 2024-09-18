// Is w an element of W_J
// w::Eltseq, J::SetEnum -> BoolElt
ElementInSubgroup := function(w, J)
    elems := Set(Eltseq(w));
    return elems subset J;
end function;

// Returns all elements of Wfin
// W::GrpFPCox -> SeqEnum
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
// J::SetEnum, datum::Tup -> Tup (SetEnum,SeqEnum,SeqEnum)
ParabolicSetup := function(J, datum)
    // Transfers elements in Wfin to the corresponding elements in W
    cosetreps := [Eltseq(x) : x in Transversal(datum[2],J)];
    Sort(~cosetreps, func<u,v|#u-#v>);
    reps := [&*[datum[1].i : i in [0] cat Eltseq(rep)] : rep in cosetreps];
    return <J, BoundingWalls(J, datum), reps>;
end function;

// Checks if there is a bounce (with respect to J)
CheckInRoots := function(path, a, roots, datum)
    rm := datum[6];
    if #path eq 0 then
        return a in roots;
    else
        return (&*[rm[i] : i in path]) * a in roots;
    end if;
end function;

// Removes bounces from path
noBounce := function(path, Jroots, datum)
    roots := datum[4];
    i := 1;
    while i le #path do
        if CheckInRoots(path[1..i-1], roots[path[i]], Jroots, datum) then
            Remove(~path,i);
        else
            i := i + 1;
        end if;
    end while;
    return path;
end function;

// Changes path (as a sequence) to a coxeter word in W
reducePath := function(path, datum)
    W := datum[1];
    if #path eq 0 then
        return W.0;
    else
        return &*[W.i : i in path];
    end if;
end function;

// Decomposes any element w into translation and finite element (in Wfin) (Returns (theta(w), wt(w)))
// w:SeqEnum, datum::tup -> Tup
transDecomp := function(w, datum)
    W := datum[1];
    h := datum[5];
    rm := datum[6];
    refl := datum[8];
    w := W ! w;

    // Record how much of each translation is needed
    trans := [0 : t in Eltseq(h)];
    while #Generators(W) in Eltseq(w) do
        // Pad out the sequence to stop empty initial or terminal sequences
        seq := [1,1] cat Eltseq(w) cat [1,1];
        idx := Index(seq, #Generators(W));
        initial := seq[1..idx-1];
        
        // Apply reflection matrices to the highest root translation
        tr := Eltseq(Transpose(&*[rm[i] : i in initial] * h));
        trans := [trans[i] + tr[i] : i in [1..#trans]];

        w := reducePath(seq[1..idx-1] cat Eltseq(refl) cat seq[idx+1..#seq], datum);
    end while;
    return <w, trans>;
end function;

// Removes fold from the path u+path+Reverse(path) and returns Coxeter element (in Wfin)
foldPath := function(u, path, k, datum, Jdatum)
    a := datum[4];
    Jroots := Jdatum[2];
    pathk := Remove(path,k);
    return reducePath(noBounce(u cat pathk cat Reverse(path), Jroots, datum), datum);
end function;

// Checks which coset an element of Wfin is in (w.r.t J)
FundamentalDomainElement := function(w, datum, Jdatum)
    reps := Jdatum[3];
    for rep in reps do
        if ElementInSubgroup(w * Inverse(rep), Jdatum[1]) then
            return rep;
        end if;
    end for;
    // Should never return false (treat as raising error)
    return false;
end function;

// Prints number in folding table after a fold
phik := function(u, path, k, datum, Jdatum)
    v := transDecomp(foldPath(Eltseq(Jdatum[3][u]), path, k, datum, Jdatum), datum)[1];
    v := FundamentalDomainElement(v, datum, Jdatum);
    return Index(Jdatum[3], v);
end function;

// Returns the u-th row of the folding table (u in W^J)
FoldingTableRow := function(u, t, datum, Jdatum)
    outputs := [" " : x in t];
    useq := Eltseq(Jdatum[3][u]);
    pos_root := [Transpose(Matrix(r)) : r in PositiveRoots(datum[3])];
    s := t;
    i := 1;
    j := 1;
    while i le #s do
        w := useq cat s[1..i-1];
        a := datum[4][s[i]];
        if CheckInRoots(w, a, Jdatum[2], datum) then
            outputs[j] := "*";
            Remove(~s, i); //Don't update i
        elif CheckInRoots(w, a, pos_root, datum) then
            outputs[j] := IntegerToString(phik(u, t[1..j], j, datum, Jdatum));
            i := i + 1;
        else
            outputs[j] := "-";
            i := i + 1;
        end if;
        j := j + 1;
    end while;
    return outputs;
end function;

intrinsic LongRoots(type::MonStgElt) -> SeqEnum
{Gives the long roots of the root datum associated to type}
    roots := Roots(RootSystem(ReflectionGroup(type)));
    longroots := [];
    for i in [1..#roots] do 
        if IsLongRoot(RootSystem(ReflectionGroup(type)),i) eq true then 
            longroots := longroots cat [Transpose(Matrix(roots[i]))];
        end if;
    end for;
    return longroots;
end intrinsic;

intrinsic ShortRoots(type::MonStgElt) -> SeqEnum
{Gives the short roots of the root datum associated to type}
    roots := Roots(RootSystem(ReflectionGroup(type)));
    shortroots := [];
    for i in [1..#roots] do 
        if IsShortRoot(RootSystem(ReflectionGroup(type)),i) eq true then 
            shortroots := shortroots cat [Transpose(Matrix(roots[i]))];
        end if;
    end for;
    return shortroots;
end intrinsic;

intrinsic LongEltSet(J::SetEnum, W::GrpFPCox) -> SeqEnum
{Gives the long element of W_J for a subset J of I}
    J := [ j : j in J];
    Sort(~J,func<v,w|v-w>);
    if #J eq 0 then
        return [];
    end if;
    irrecomp, irrecompsing := GraphJRtDat(J, W);
    coxsys := {<CoxeterGroup(GrpFPCox,x[1]),x[2]> : x in irrecomp} join {<CoxeterGroup(GrpFPCox,x[1]),x[2]> : x in irrecompsing};
    longelt := {<Eltseq(LongestElement(x[1])),x[2]> : x in coxsys};
    longelt := {<x[1], J[x[2]]> : x in longelt};
    wJ := [];
    for x in longelt do
        wJ := wJ cat [x[2][i]: i in x[1]];
    end for;
    return wJ;
end intrinsic;

intrinsic FoldingTable(t::SeqEnum, type::MonStgElt, J::SetEnum)
{Prints folding table}
    datum := CoxeterSetup(type);
    Jdatum := ParabolicSetup(J, datum);
    t;
    for u in [1..#Jdatum[3]] do
        <FoldingTableRow(u, t, datum, Jdatum), u>;
    end for;
end intrinsic;

intrinsic FoldingTableWrite(t::SeqEnum, type::MonStgElt, J::SetEnum, file::MonStgElt)
{Writes folding table to a txt file}
    datum := CoxeterSetup(type);
    Jdatum := ParabolicSetup(J, datum);
    if #J eq 0 then Write(file, type cat " " cat "{" cat "}");
    else Write(file, type cat " " cat "{" cat &cat([IntegerToString(x) cat "," : x in J])cat "}");
    end if;
    Write(file, &cat([IntegerToString(x) cat "," : x in t]));
    for u in [1..#Jdatum[3]] do
        Write(file, &cat([x cat "," : x in FoldingTableRow(u, t, datum, Jdatum)]));
    end for;
    "Wrote to " cat file cat "!";
end intrinsic;