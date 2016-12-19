// this file contains some useful subroutines 


             /*--- Jordan form functions ---*/

/*
   Given an irreducible polynomial <p> over a field <k>,
   and a <partition>, construct the generalised Jordan
   block determined by these parameters.
   
   This is not the standard Magma form.
*/

__build_JF := function (p, partition)
     Cp := CompanionMatrix (p);
     s := #partition;
     m := &+ partition;
     k := BaseRing (Parent (p));
     d := Degree (p);
     IdBlock := Identity (MatrixAlgebra (k, d));
     JF := DiagonalJoin (< Cp : i in [1..m] >);
     mm := 1;      
     for i in [1..s] do
         mi := partition[i];
         for j in [1..mi - 1] do
	     InsertBlock (~JF, IdBlock, mm, mm + d);
             mm +:= d;
	 end for;
         mm +:= d;
     end for;
return JF;
end function;


/*
   Given a primary matrix <P>, return the generalized 
   Jordan normal form of <P> and the partition
   associated with the invariant factors of <P>
*/

__primary_JF := function (P)

     k := BaseRing (Parent (P));

     // first conjugate <P> to Magma JNF
     J, D := JordanForm (P);

     mpol := MinimalPolynomial (J);
     mfac := Factorisation (mpol);

     if (#mfac gt 1) then
        error "<P> must be primary";
     end if;
  
     p := mfac[1][1];
     ifacs := InvariantFactors (J);
     partition := [ Factorisation (ifacs[i])[1][2] : 
                                      i in [1..#ifacs] ];

     if (Degree (p) gt 1) then   
       
	 /* build the (primary) Jordan form for given parameters */
         JF := __build_JF (p, partition);
         J, C := JordanForm (JF);
         D := C^-1 * D;
         
     else

         /* My Jordan form agrees with the one used by Magma */       
         JF := J;
    
     end if;     
     
return JF, D, partition;
end function;


/* a partition ordering function */

__le_partition := function (part1, part2)
     if part1 eq part2 then return true; end if;
     if #part1 lt #part2 then return true; end if;
     if #part1 gt #part2 then return false; end if;
     i := Min ({ j : j in [1..#part1] | part1[j] ne part2[j] });
return part1[i] lt part2[i];
end function;


/*  
   Builds the generalized Jordan Normal Form of X with blocks 
   appearing in increasing order of min poly degree, and within 
   each min poly degree, "increasing" order of partition.

   This modification of an earlier function was written in
   Fort Collins in December, 2014.
*/

JordanNormalForm := function (X)

     d := Nrows (X);
     k := BaseRing (Parent (X));
     mfac := Factorisation (MinimalPolynomial (X));
     degs := { Degree (mfac[i][1]) : i in [1..#mfac] };
     degs := [ m : m in degs ];
     ordered := [ [ mfac[i] : i in [1..#mfac] | Degree (mfac[i][1]) eq m ] : m in degs ];

     /* proceed sequentially through the primary components */
     info := [* *];
     basis := [ ];
     
     for j in [1..#degs] do
     
         nullspaces := [* *];
         transition_matrices := [* *];
         partitions := [* *];
         pols := [* *];
         
         for i in [1..#ordered[j]] do
	       
	     pi := ordered[j][i][1];
             Append (~pols, pi);
             ei := ordered[j][i][2];
             fi := pi^ei;   
             Xi := Evaluate (fi, X);
             Vi := Nullspace (Xi);
             Append (~nullspaces, Vi);
             di := Dimension (Vi);
           
             /* restrict <Xi> to <Vi> to get a primary matrix <Pi> */
             rows := [ Coordinates (Vi, (Vi.j) * X) : j in [1..di] ];
             Pi := Matrix (rows);
           
             Ji, Ci, parti := __primary_JF (Pi);
             Append (~transition_matrices, Ci);
             Append (~partitions, parti);
           
         end for;
     
         /* put partitions into a standard order */         
         index := { 1 .. #partitions };
         order := [ ];         
         while #order lt #partitions do
             assert exists (s){ t : t in index | 
                  forall { u : u in index | __le_partition (partitions[t], partitions[u]) } };
             Append (~order, s);
             Exclude (~index, s);
         end while;
     
         /* select basis to exhibit Jordan structure */
         for i in order do
             Ci := transition_matrices[i];
             Vi := nullspaces[i];
             di := Dimension (Vi);
             bas := [ &+ [ Ci[s][t] * Vi.t : t in [1..di] ] : s in [1..di] ];         
             basis cat:= bas;
             Append (~info, < pols[i], partitions[i] >);
         end for;
         
     end for;
     
     C := Matrix (basis);
     J := C * X * C^-1;
     
return J, C, info;    

end function;



/* internal function to compute block permutation matrices */
__permutation_matrix := function (blocks, pi)
     d := &+ [ Nrows (blocks[i]) : i in [1..#blocks] ];
     positions := [1] cat [ 1 + &+ [ Nrows (blocks[j]) : j in [1..i-1] ] : i in [2..#blocks] ];  
     P := MatrixAlgebra (BaseRing (Parent (blocks[1])), d)!0;
     for i in [1..#blocks] do
	   j := i^pi;
           assert Nrows (blocks[i]) eq Nrows (blocks[j]);
           InsertBlock (~P, blocks[i], positions[i], positions[j]);
     end for;
return P;
end function;



            /*--- functions for computing with fields ---*/


/* analogue of "Eltseq" that allows one to specify basis */
EltseqWithBasis := function (K, k, bas, x)
     assert #bas eq (Degree (K) div Degree (k));
     W, g := VectorSpace (K, k);
     U := VectorSpaceWithBasis ([ bas[i] @ g : i in [1..#bas] ]);
return Coordinates (U, x @ g);
end function;


/* 
  given <T> acting irreducibly on its underlying module, return 
  inverse isomorphsisms from Env(<T>) to the isomorphic field.
  Also return a generator for Gal(Env(<T>)).
*/
IsomorphismWithField := function (T)

     assert T ne 0;

     /* use min poly of T to build extension */
     mT := MinimalPolynomial (T);
     assert IsIrreducible (mT);
     e := Degree (mT);
     assert e eq Nrows (T);
     k := BaseRing (Parent (T));
     K := ext < k | mT >;

     /* build inverse isomorphisms */
     Kbas := [ (K.1)^i : i in [0..e-1] ];
     Tbas := [ T^i : i in [0..e-1] ];
     MS := KMatrixSpace (k, e, e);
     MS := KMatrixSpaceWithBasis ([ MS!(Tbas[i]) : i in [1..e] ]);
     EnvT := sub < Parent (T) | T >; 
     phi := hom < EnvT -> K | x :-> &+ [c[i] * Kbas[i] : i in [1..e]]
            where c := Coordinates (MS, MS!x) >;
     psi := hom < K -> EnvT | x :-> &+ [c[i] * Tbas[i] : i in [1..e]]
            where c := EltseqWithBasis (K, k, Kbas, x) >;

     /* build Galois generator */
     J, C := JordanForm (T);
     u := VectorSpace (k, e).1;
     q := #k;
     gamma := Matrix ([ u * J^(q*i) : i in [0..e-1] ]);
     gamma := GL (e, k)!gamma;
     assert Order (gamma) eq e;
     gal := C^-1 * gamma * C;

          /* sanity check */
          assert gal * T * gal^-1 in sub < Parent (T) | T >;

return EnvT, K, phi, psi, gal;
end function;


/*
  given <T1> and <T2> acting irreducibly on their (common) underlying module,
  return a transition matrix conjugating Env(<T1>) to Env(<T2>)

  This algorithm was communicated to us by W.M. Kantor.
*/
IsomorphismBetweenFields := function (T1, T2)

     assert Nrows (T1) eq Nrows (T2);

     if Nrows (T1) eq 1 then
         return Identity (MatrixAlgebra (BaseRing (Parent (T1)), 1));
     end if;

     m1 := MinimalPolynomial (T1);
     assert IsIrreducible (m1);
     ET2, K2, phi2, psi2 := IsomorphismWithField (T2);

     /* factor <m1> over <K2> */
     R2 := PolynomialRing (K2);
     m1K2 := R2!m1;
     roots := Roots (m1K2);

     /* take any root and pull back to ET2 */
     alpha := roots[1][1];
     assert alpha in K2;
     X2 := alpha @ psi2;
     assert MinimalPolynomial (X2) eq m1;

     /* conjugate Env(<T1>) to Env(<X1>) = Env(<T2>) by module isomorphism */
     M1 := RModule (sub < Parent (T1) | T1 >);
     M2 := RModule (sub < Parent (X2) | X2 >);
     isit, C := IsIsomorphic (M1, M2);
     assert isit;

return C^-1;
end function;



     /*--- internal function to compute tensor over adjoint algebra ---*/
     
     

     

/*
  This function is only to be used internally, for our specific purposes.

  Input: 
     (1) <X> is a list of pairs, consisting of [ a , a* ] as the a's run
         through a basis of a *-algebra <A>.
     (2) <Rgen> is a generator for the center of <A>.

  Output:
     (1) The space <V> \otimes_<A> <V>, where <V> is the natural <A>-module.
         This is returned just as a row space of vectors written relative to
         a basis obtained from the action of <Rgen> on <V>.
     (2) A map <pi> from the tensor square of <V> to this space.
     (3) A pair of vectors in V from which basis was obtained
*/

__tensor_over_adj := function (X, Rgen)

     k := BaseRing (Parent (Rgen));
     d := Degree (Parent (Rgen));
     V := VectorSpace (k, d);
     T2V := VectorSpace (k, d^2);
     m := Degree (MinimalPolynomial (Rgen));

     /* form the tensor product over A */
     count := 1;
     found := false;
     while (count le 20) and (not found) do

        // seems best to do this randomly ... talk to James about this
        rels := [ ];
        for i in [1..d^2-m] do
            u := Random (V);
            v := Random (V);
            c := [ Random (k) : j in [1..#X] ];
            a := &+ [ c[j] * X[j][1] : j in [1..#X] ];
            aa := &+ [ c[j] * X[j][2] : j in [1..#X] ];
            Append (~rels, TensorProduct (u * a, v) - TensorProduct (u, v * aa));
        end for;

        Z := sub < T2V | rels >;
        codim := d^2 - Dimension (Z);
        
        if codim eq m then 
            found := true;
        end if;

        count +:= 1;

     end while;

     if not found then
     "...randomized aspect of tensor over adj failed";
         return false, _, _, _;
     end if;


     W, pi := T2V / Z;
     assert Dimension (W) eq m;

         /* find a basis for W using the action of Rgen on V */
         found := false;
         count := 0;
         LIMIT := 100;
         while (not found) and (count lt LIMIT) do
             count +:= 1;
             u := Random (V);
             v := Random (V);
             bas := [ TensorProduct (u, v * Rgen^i) @ pi : i in [0..m-1] ];
             if sub < W | bas > eq W then
                 found := true;
             end if;
         end while;

         assert Degree (bas[1]) eq m;
         if #Set (bas) ne m then
             "...randomized aspect of tensor over adj failed";
             return false, _, _, _;
         end if;

         /* modify <pi> so that images are written relative to <bas> */
         U := VectorSpaceWithBasis (bas);
         pi := hom < T2V -> W | x :-> W!Coordinates (U, x @ pi) >;

             // basis sanity check ...
             assert  forall { i : i in [0..m-1] | 
                        TensorProduct (u, v * Rgen^i) @ pi eq W.(i+1) };

return true, W, pi, [u,v];

end function;


/*
   Given a <system> of forms representing an hermitian bimap,
   determine whether or not the bimap is a tensor product.
*/

IsTensor_Deterministic := function (system)

     /* compute the dimension of <system> */
     k := BaseRing (Parent (system[1]));
     d := Degree (Parent (system[1]));
     MS := KMatrixSpace (k, d, d);
     m := Dimension (sub < MS | [ MS!F : F in system ] >);

     /* form the tensor product over the adjoint algebra of <system> */
     A := AdjointAlgebra (system);
     V := VectorSpace (k, d);
     T2V := VectorSpace (k, d^2);
     rels := [ ];
     for i in [1..d] do
         for j in [1..d] do
            rels cat:= [ TensorProduct (V.i * A.l, V.j) - 
              TensorProduct (V.i, V.j * (A.l @ A`Star)) : l in [1..Ngens (A)] ];
         end for;
     end for;
     Z := sub < T2V | rels >;
     W, pi := T2V / Z;
     
return m eq Dimension (W);

end function;



GenericTensorProduct := function (X : dimension := false, alternating := false,
                                      group := false)

     k := BaseRing (Parent (X[1][1]));
     d := Degree (Parent (X[1][1]));
     V := VectorSpace (k, d);
     T2V := VectorSpace (k, d^2);

     /* form the tensor product over A */
     count := 1;
     found := false;
     
     if Type (dimension) eq BoolElt then
         LIMIT := 2*d^2;
     else
         assert Type (dimension) eq RngIntElt;
         LIMIT := d^2 - dimension;
     end if;
     
     while (count le 20) and (not found) do

        rels := [ ];
        for i in [1..LIMIT] do
            u := Random (V);
            v := Random (V);
            c := [ Random (k) : j in [1..#X] ];
            a := &+ [ c[j] * X[j][1] : j in [1..#X] ];
            aa := &+ [ c[j] * X[j][2] : j in [1..#X] ];
            Append (~rels, TensorProduct (u * a, v) - TensorProduct (u, v * aa));
        end for;
        
        if alternating then
            arels := [ TensorProduct (V.i, V.j) + TensorProduct (V.j, V.i) : 
                       i in [1..Ngens (V)], j in [1..Ngens (V)] ];
            rels cat:= arels;
        end if;
        
        Z := sub < T2V | rels >;
        
        if Type (dimension) eq BoolElt then
            found := true;
        else
            found := (Dimension (Z) eq LIMIT);
        end if;
        
        count +:= 1;

     end while;
     
     if not found then
         "randomized tensor product procedure failed ... check dimension parameter";
         return false, _, _;
     end if;

     W, pi := T2V / Z;

return true, W, pi;

end function;


       /*--- generic stabiliser functions ---*/

/*
  <G> is a subgroup of GL(d,k)
  <S> is a set of d x d matrices over k
  return the subgroup of <G> that stabilises the 
      k-span of <S> under conjugation.
*/
StabiliserOfMatrixSpace := function (G, S)

     d := Degree (G);
     k := BaseRing (G);

     /* compute action of <G> on the full space of d x d matrices */
     MS := KMatrixSpace (k, d, d);
     gens := [ ];
     for i in [1..Ngens (G)] do
	     g := G.i;
         rows := [ ];
         for j in [1..d^2] do
	         mat_jg := Matrix (g^-1) * MS.j * Matrix (g);
             Append (~rows, Coordinates (MS, mat_jg)); 
         end for;
         Append (~gens, GL (d^2, k)!Matrix (rows));
     end for;
     H := sub < GL (d^2, k) | gens >;
     H`UserGenerators := gens;
     

     /* coerce <S> into k^(d^2) and compute stabiliser there */
     SS := [ VectorSpace (k, d^2)!Coordinates (MS, MS!(S[l])) : l in [1..#S] ];
     U := sub < VectorSpace (k, d^2) | SS >;
     LOW, HIGH, EST := EstimateOrbit (H, U);
     if (EST gt 10^7) or (EST eq 0) then
          return false, _;
     end if;
     isit := RandomSchreierBounded (H, 10^7);
     if not isit then
          return false, _;
     end if;
     stH := Stabiliser (H, U);
     tt := Cputime ();
     n := Index (H, stH);
     
     /* efficiently find preimage of <stH> */
     f := InverseWordMap (H);
     positions := [ Position (H`UserGenerators, H.i) : i in [1..Ngens (H)] ];
     st_gens := [ Evaluate (stH.i @ f , 
                  [ G.(positions[j]) : j in [1..#positions] ]) :
                    i in [1..Ngens (stH)] ];
     stG := sub < Generic (G) | st_gens >;
     stG`Order := G`Order div n;   // assume <Order> is assigned for <G>

return true, stG;
end function;


       /*--- some useful functions for algebras ---*/


/*----- the conjugacy test -----*/

/*
   given arbitrary <T1> and k[<T2>], determine whether or not <T1> can be
   conjugated into k[<T2>] and, if so, find a C that does the trick.
*/

IsConjugateCyclic := function (T1, R)

     T2 := R.1;
     MA := Generic (R);
     d := Degree (MA);

     J1, C1, info1 := JordanNormalForm (T1);
     J2, C2, info2 := JordanNormalForm (T2);

     I1 := [ < Degree (info1[i][1]) , info1[i][2] > : i in [1..#info1] ];
     I2 := [ < Degree (info2[i][1]) , info2[i][2] > : i in [1..#info2] ];

     if I1 ne I2 then 
         return false, _; 
     end if;
     
     /* conjugate the primary components */
     pos := 1;
     blocks := < >;
     for i in [1..#info1] do
     
	  di := Degree (info1[i][1]);
          parti := info1[i][2];
     
          /* find the basic field isomorphism */
          Ti1 := ExtractBlock (J1, pos, pos, di, di);
          Ti2 := ExtractBlock (J2, pos, pos, di, di);
          Di := IsomorphismBetweenFields (Ti1, Ti2);
     
          /* propogate basic iso to the other blocks in primary component */
          ni := &+ parti;
          Ci := DiagonalJoin (< Di : i in [1..ni] >);
          Append (~blocks, Ci);
          
          pos +:= di * ni;
     
     end for;
     
     C := DiagonalJoin (blocks);
     assert Nrows (C) eq d;
     
     C := C2^-1 * C * C1;
     if not C * T1 * C^-1 in R then
         return false, _;
     end if;

return true, C;

end function;

