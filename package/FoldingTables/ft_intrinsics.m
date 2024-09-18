

// Gives the long roots of the root datum associated to type
LongRoots := intrinsic(type::MonStgElt) -> SeqEnum
    roots := Roots(RootSystem(ReflectionGroup(type)));
    longroots := [];
    for i in [1..#roots] do 
        if IsLongRoot(RootSystem(ReflectionGroup(type)),i) eq true then 
            longroots := longroots cat [Transpose(Matrix(roots[i]))];
        end if;
    end for;
    return longroots;
end intrinsic;

// Gives the short roots of the root datum associated to type
ShortRoots := intrinsic(type::MonStgElt) -> SeqEnum
    roots := Roots(RootSystem(ReflectionGroup(type)));
    shortroots := [];
    for i in [1..#roots] do 
        if IsShortRoot(RootSystem(ReflectionGroup(type)),i) eq true then 
            shortroots := shortroots cat [Transpose(Matrix(roots[i]))];
        end if;
    end for;
    return shortroots;
end intrinsic;

// Gives the long element of W_J for a subset J of I
LongEltSet := intrinsic(J::SetEnum, W::GrpFPCox) -> SetEnum
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

// Prints folding table
// t::SeqEnum, type::MonStgElt, J::SeqEnum
FoldingTable := procedure(t, type, J)
    datum := CoxeterSetup(type);
    Jdatum := ParabolicSetup(J, datum);
    t;
    for u in [1..#Jdatum[3]] do
        <FoldingTableRow(u, t, datum, Jdatum), u>;
    end for;
end procedure;

// Writes folding table to a txt file 
FoldingTableWrite := procedure(t, type, J, file) 
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
end procedure;