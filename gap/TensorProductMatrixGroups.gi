# Construction as in Proposition 7.1 of [2]
BindGlobal("TensorProductStabilizerInSL",
function(d1, d2, q)
    local d, c, k, g, zeta, C, Id1, Id2, gens, SLd1Gens, SLd2Gens,
    diagonalGenerator1, diagonalGenerator2, solution, result;
    if not d1 < d2 then
        ErrorNoReturn("<d1> must be less than <d2> but <d1> = ", d1, 
                      " and <d2> = ", d2);
    fi;

    d := d1 * d2;
    k := Gcd(d, q - 1);
    g := Gcd(d1, d2, q - 1);
    c := QuoInt(Gcd(d1, q - 1) * Gcd(d2, q - 1) * g, k);
    zeta := PrimitiveElement(GF(q));
    C := zeta^(QuoInt((q - 1), k)) * IdentityMat(d, GF(q)); # generates the center of SL(d, q)
    Id1 := One(SL(d1 ,q));
    Id2 := One(SL(d2 ,q));

    gens := [C];
    SLd1Gens := GeneratorsOfGroup(SL(d1, q));
    SLd2Gens := GeneratorsOfGroup(SL(d2, q));
    Add(gens,KroneckerProduct(SLd1Gens[1], Id2)); # corresponds to S in [2]
    Add(gens,KroneckerProduct(SLd1Gens[2], Id2)); # corresponds to T in [2]
    Add(gens,KroneckerProduct(Id1, SLd2Gens[1])); # corresponds to U in [2]
    Add(gens,KroneckerProduct(Id1, SLd2Gens[2])); # corresponds to V in [2]

    if not c = 1 then
        diagonalGenerator1 := GL(d1, q).1; # diagonal matrix [zeta, 1, ..., 1]
        diagonalGenerator2 := GL(d2, q).1;
        # Solving the modular congruence d2 * x + d1 * y = 0 mod (q - 1) by
        # solving the matrix equation (d2, d1, q - 1) * (x, y, t) = 0 over the
        # integers.
        for solution in NullspaceIntMat([[d2], [d1], [q - 1]]) do
            Add(gens, 
                KroneckerProduct(diagonalGenerator1 ^ solution[1],
                                 diagonalGenerator2 ^ solution[2]));
        od;
    fi;

    result := Group(gens);
    # Size according to Table 2.7 in [1]
    SetSize(result, Size(SL(d1, q)) * Size(SL(d2, q)) * g);
    return result;
end);
