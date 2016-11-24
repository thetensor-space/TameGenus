
/* this file contains functions to compute pseudo-isometries of flat bimaps of corank 2 */


/*
   build the standard flat, indecomposable pair:
   
       X = [  0_m  I_m  0 ]    and   Y = [  0_m  0  I_m ]
           [ -I_m  0_m  0 ]              [   0   0   0  ]
           [   0    0   0 ]              [ -I_m  0  0_m ]
*/

__StandardFIPair := function (k, m)
     MA := MatrixAlgebra (k, 2*m+1);
     ma := MatrixAlgebra (k, m);
     X := MA!0;   
     InsertBlock (~X, Identity (ma), 1, m+1);
     InsertBlock (~X, -Identity (ma), m+1, 1);
     Y := MA!0;
     InsertBlock (~Y, Identity (ma), 1, m+2);
     InsertBlock (~Y, -Identity (ma), m+2, 1);
return X, Y;
end function;


/*
  Input: a field <k> and an integer <m>

  Output: The group of pseudo-isometries of the standard 
  flat, indecomposable pair 
*/

__PseudoIsometryGroupStandardFIPair := function (k, m)
     
     X, Y := __StandardFIPair (k, m);
     
     G := GL (2*m+1, k);
     gens := [ ];
     
     Zsmall := MatrixAlgebra (k, m)!0;
     Zlarge := MatrixAlgebra (k, m+1)!0;
     
     /* 
         first the action of 
         
         [ a 0 ]
         [ 0 1 ]
     */
     S := Zsmall;
     T := Zlarge;
     a := PrimitiveElement (k);
     for i in [0..m] do
        T[m+1-i][m+1-i] := a^i;
     end for;
     b := 1/a;
     for i in [0..m-1] do
        S[m-i][m-i] := b^i;
     end for;
     Append (~gens, G!DiagonalJoin (S, T));
     
     /* 
         next the action of 
         
         [ 0 1 ]
         [ 1 0 ]
     */
     
     S := Zsmall;
     T := Zlarge;
     for i in [1..m] do
        S[i][m+1-i] := 1;
     end for;
     for i in [1..m+1] do
        T[i][m+2-i] := 1;
     end for;
     Append (~gens, G!DiagonalJoin (S, Transpose (T^-1)));
     
     /* 
         Finally the action of 
         
         [ 1 1 ]
         [ 0 1 ]
     */
     
     T := Zlarge;
     for i in [1..m] do
         for j in [i..m+1] do
             T[i][j] := (-1)^(i+j) * Binomial (m+1-i,m+1-j);
         end for;
     end for;
     T[m+1][m+1] := 1;
     S := ExtractBlock (T, 2, 2, m, m);
     Append (~gens, G!DiagonalJoin (S, Transpose (T^-1)));
     
     /* sanity check */
     MS := KMatrixSpace (k, 2*m+1, 2*m+1);
     MS := KMatrixSpaceWithBasis ([MS!X, MS!Y]);
     "    __PIGSFIP check:",
        forall { g : g in gens | 
             forall { i : i in [1..Ngens (MS)] | g * MS.i * Transpose (g) in MS } };

return gens;

end function;


/*
  Given an alternating bimap Bi defining a flat
  indecomposable bimap of corank 2, find a matrix conjugating 
  Bi to the standard flat, indecomposable pair.
*/

__TransformFIPair := function (Bi)
     F := SystemOfForms(Bi)[1];
     G := SystemOfForms(Bi)[2];
     k := BaseRing (Bi);

     d := Dimension(Bi`Domain[1]);
     assert d mod 2 eq 1;
     m := (d - 1) div 2;

     /* find complementary t.i. subspaces */
     
     A := AdjointAlgebra (Bi); // Make sure to get all the star info
     J, T := TaftDecomposition (A);
     mins := MinimalIdeals (T);
     assert #mins eq 2;
     I1 := mins[1];
     I2 := mins[2];
     assert Dimension (I1) eq Dimension (I2);
     ims := [ Image (I1.1) , Image (I2.1) ];
     assert exists (E){ U : U in ims | Dimension (U) eq m };
     assert exists (Eop){ U : U in ims | Dimension (U) eq m+1 };
     
     C1 := Matrix (Basis (E) cat Basis (Eop));
     X := C1 * F * Transpose (C1);
     Y := C1 * G * Transpose (C1);
     C := C1;
     
     
     /* transform X1 to standard form */
     
     F0 := ExtractBlock (X, 1, m+1, m, m+1);
     S, U, V := SmithForm (F0);
     assert Rank (S) eq m;
     C2 := Generic (A)!0;
     InsertBlock (~C2, U, 1, 1);
     InsertBlock (~C2, Transpose (V), m+1, m+1);
     X := C2 * X * Transpose (C2);
     Y := C2 * Y * Transpose (C2);
     C := C2 * C;
     
     /* we have:
     
       <X> = [ 0_m  I_m  0 ]  and <Y> = [  0_m     U     ]
             [-I_m  0_m  0 ]            [ -U^t   0_(m+1) ]
             [  0    0   0 ]  
             
       where  U = [  U0  u^t  ]
                  
       we next conjugate U0 to its companion matrix
     */ 
     
     U0 := ExtractBlock (Y, 1, m+1, m, m);
     R, B := RationalForm (U0);
     C3 := Identity (Generic (A));
     InsertBlock (~C3, B, 1, 1);
     InsertBlock (~C3, Transpose (B^-1), m+1, m+1);
     X := C3 * X * Transpose (C3);
     Y := C3 * Y * Transpose (C3);
     C := C3 * C;


     /* next we find T in Env(R) sending u^t to (0 0 ... 0 1)^t */
     
     u := Vector (Transpose (ExtractBlock (Y, 1, d, m, 1)));
     uRbas := [ u*Transpose (R)^i : i in [0..m-1] ];
     V := VectorSpaceWithBasis (uRbas);
     e := V!0;
     e[m] := 1;
     c := Coordinates (V, e);
     P := &+[ c[i] * R^(i-1) : i in [1..m] ];
     C4 := Identity (Generic (A));
     InsertBlock (~C4, P, 1, 1);
     InsertBlock (~C4, Transpose (P^-1), m+1, m+1);
     X := C4 * X * Transpose (C4);
     Y := C4 * Y * Transpose (C4);
     C := C4 * C;


     /* we now have:

        U = [ 0   I_(m-1)   0  ]
            [ b      v      1  ] 
    
        and we just have to strip away the detritus
     */
     
     v := ExtractBlock (Y, m, m+1, 1, m);
     C5 := Identity (Generic (A));
     InsertBlock (~C5, -Transpose (v), m+1, d);
     X := C5 * X * Transpose (C5);
     Y := C5 * Y * Transpose (C5);
     C := C5 * C;

     /* sanity check */
     XX, YY := __StandardFIPair (k, m);
     assert (X eq XX) and (Y eq YY);
     
return C;
     
end function;




/* 
Based off of a discussion with Pete.
*/

/*
Constructs a lift for:
[ a 0 ]
[ 0 1 ]
*/

__DiagonalFlat := function( k, n, a )
	m := (n-1) div 2;
	MA := MatrixAlgebra( k, n );
	S := MatrixAlgebra(k, m)!0;
	T := MatrixAlgebra(k, m+1)!0;
	for i in [0..m] do
		T[m+1-i][m+1-i] := a^i;
	end for;
	b := 1/a;
	for i in [0..m-1] do
		S[m-i][m-i] := b^i;
	end for;
	return MA!DiagonalJoin(S, T);
end function;

/*
Given Z in GL(2,K), construct a lift of Z 
for a standard flat pair of dimension n.
*/

__LiftFlatGenus2 := function( Z, n );
	assert Ncols(Z) eq 2;
	a := Z[1][1];
	b := Z[1][2];
	c := Z[2][1];
	d := Z[2][2];
	k := Parent(a);
	MA := MatrixAlgebra( k, n ); 
	m := (n-1) div 2;
	Ints := Integers();

	Zsmall := MatrixAlgebra (k, m)!0;
	Zlarge := MatrixAlgebra (k, m+1)!0;

	S := Zsmall;
	T := Zlarge;
	for i in [1..m] do
		S[i][m+1-i] := 1;
	end for;
	for i in [1..m+1] do
		T[i][m+2-i] := 1;
	end for;
	Perm := MA!DiagonalJoin(S, Transpose (T^-1));

	T := Zlarge;
	for i in [1..m] do
		 for j in [i..m+1] do
		     T[i][j] := (-1)^(i+j) * Binomial (m+1-i,m+1-j);
		 end for;
	end for;
	T[m+1][m+1] := 1;
	S := ExtractBlock (T, 2, 2, m, m);
	Trans := MA!DiagonalJoin(S, Transpose (T^-1));
	Trans := Perm * Trans * Perm;

	if c eq 0 then
		/*
      Z = [ 0 1 ] [ d 0 ] [ 0 1 ] [ a 0 ] [ 1 1 ]^(b/a mod p)
          [ 1 0 ] [ 0 1 ] [ 1 0 ] [ 0 1 ] [ 0 1 ] 
		*/
		X := Perm * __DiagonalFlat( k, n, d ) * Perm * __DiagonalFlat( k, n, a) * Trans^(Ints!(b/a));
	else
		/*
      Z = [ b - ad/c  0 ] [ 1 1 ]^(a/(bc-ad) mod p) [ 0 1 ] [ c 0 ] [ 1 1 ]^(d/c mod p)
          [    0      1 ] [ 0 1 ]                   [ 1 0 ] [ 0 1 ] [ 0 1 ]
		*/
		X := __DiagonalFlat( k, n, b - a*d/c ) * Trans^(Ints!(a/(b*c-a*d))) * Perm * __DiagonalFlat( k, n, c ) * Trans^(Ints!(d/c));
	end if;
	
  F1,F2 := __StandardFIPair(k,m);
  assert [ X*F1*Transpose(X), X*F2*Transpose(X) ] eq [ &+[ Z[1][i]*F1, Z[2][i]*F2 ] : i in [1..2] ];

	return X;
end function;
