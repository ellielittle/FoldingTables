
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

