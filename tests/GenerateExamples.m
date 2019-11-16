RunTameGenusTest := function(N)
    SetVerbose("TameGenus", 2);
    GradCat := TensorCategory([1, 1, 1], {{1, 2}, {0}});
    RandTensor := function()
        repeat // Avoids an error that we cannot fix. 
            K := GF(Random([3, 5, 9, 11, 25, 125, 243]));
            d := Random([4..14]);
            r := Random([0..3]);
            c := Random([0..3]);
            "Parameters: ", [*K, d, r, c*];
            Forms := SystemOfForms(RandomAlternatingTensor(K, d, 2, 2));
            Forms := [DiagonalJoin(X, ZeroMatrix(K, r, r)) : X in Forms];
            Forms cat:= [ZeroMatrix(K, d + r, d + r) : i in [1..c]];
            X := Random(GL(d + r, K));
            Y := Random(GL(2 + c, K));
            H := Homotopism([*X, X, Y*], TensorCategory([1, 1, -1], {{2, 1}, {0}}));
            t := Tensor(Forms, 2, 1, GradCat);
        until IsIndecomposable(FullyNondegenerateTensor(t)); 
        return t, t @ H;
    end function;

    for i in [1..N] do
        // t and s are built to be iso, but u is very likely not iso.
        t, s := RandTensor();
        u := RandTensor();
        G := HeisenbergGroupPC(t);
        H := HeisenbergGroupPC(s);
        K := HeisenbergGroupPC(u);

        // Test 1: Groups and automorphisms
        try
            A := TGAutomorphismGroup(G);
        catch e
            "TGAutomorphismGroup Error";
            return [*G*];
        end try;

        // Test 2: Groups and isomorphism
        try
            isit := TGIsIsomorphic(G, H);
            if not isit then
                "Expected groups to be isomorphic";
                return [*G, H*];
            end if;
        catch e
            "TGIsIsomorphic Error (true)";
            return [*G, H*];
        end try;

        // Test 3: Groups and non isomorphism
        try
            isit := TGIsIsomorphic(G, K);
        catch e
            "TGIsIsomorphic Error";
            return [*G, K*];
        end try;
    end for;
    "Passed!";
    return 0;
end function;
