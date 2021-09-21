# Return the subgroup of <M>SL(n, q)</M> stabilising a
# decomposition <M>F^n=V_1\oplus V_2\oplus\dots\oplus V_t</M> of <M>F^n</M>,
# where <C>F := GF(q)</C>, as a direct sum of vector spaces of equal
# dimensions. Note that this means that <A>t</A> must be a divisor of <A>n</A>.
# We demand that <A>t</A> be greater than 1.
# Construction as in Proposition 5.1 of [2]
BindGlobal("ImprimitivesMeetSL", 
function(n, q, t)
    local det, E, gens, i, newGen, newGens, wreathProduct, z, m, result;
    if t = 1 or (n mod t) <> 0 then
        ErrorNoReturn("<t> must be greater than 1 and a divisor of <n> but <t> = ", t,
                      " and <n> = ", n);
    fi;
    m := QuoInt(n, t);
    wreathProduct := MatWreathProduct(SL(m, q), SymmetricGroup(t));
    gens := GeneratorsOfGroup(wreathProduct);
    # newGens will be analogous to A, B, C, D in [2]
    newGens := [];
    for i in [1..Length(gens)] do
        det := Determinant(gens[i]);
        if IsOne(det) then
            Add(newGens, gens[i]);
        else
            # rescale first column by -1
            newGen := gens[i] * DiagonalMat(Z(q) ^ 0
                * Concatenation([-1], List([2..n], i -> 1)));
            Add(newGens, newGen);
        fi;
    od;
    z := PrimitiveElement(GF(q));
    E := DiagonalMat(
        Concatenation([z], List([2..m], i -> z ^ 0),
                      [z ^ -1], List([m + 2..n], i -> z ^ 0))
    );
    Add(newGens, E);
    result := Group(newGens);
    # Size according to Table 2.5 of [1]
    SetSize(result, Size(SL(n/t, q)) ^ t * (q-1) ^ (t-1) * Factorial(t));
    return result;
end);
