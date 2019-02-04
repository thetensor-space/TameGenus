/* 
    Copyright 2015--2017, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/



/*
Input two pairs of systems of alternating forms B1=[F1,G1], B2=[F2,G2] over k
if there exists pseudo-isometry (X,Z) such that 
X * B1 * Tranpose(X) = B2^Z,
returns true and (X,Z). Returns false otherwise.
*/

import "Flat.m": __TransformFIPair, __LiftFlatGenus2;
import "Util.m": __PGL2PermToMat, __GL2ActionOnPolynomial, __PermutationDegreeMatrix, __FindPermutation, __GetStarAlg, __WriteMatrixOverPrimeField;
import "LiftPoly.m": __LiftSlopeGenus2;

__Pfaffian_ISO := function( bB, bC, flats, sloped : Sanity := false )
	k := BaseRing(bB);
  sorted_dims := flats cat sloped;
  si := #flats + 1;

	// The bimaps are in block diagonal form, we extract the top right corners of the sloped
  // and the bimap (along with adj) of the flats.
  BB1 := SystemOfForms(bB);
  BB2 := SystemOfForms(bC);
  Flat_Bimaps1 := [**];
  Flat_Bimaps2 := [**];
	TRX1 := [**];
	TRY1 := [**];
	TRX2 := [**];
	TRY2 := [**];
  d := sorted_dims;
  start := 1;
	for i in [1..#d] do
    if i lt si then //flat 
      temp1 := Tensor( [ ExtractBlock(X, start, start, d[i], d[i]) : X in BB1 ], 2, 1 );
      temp2 := Tensor( [ ExtractBlock(X, start, start, d[i], d[i]) : X in BB2 ], 2, 1 );
      temp1`Adjoint := __GetStarAlg( AdjointAlgebra(bB), IdentityMatrix(k,&+sorted_dims), start, d[i] );
      temp2`Adjoint := __GetStarAlg( AdjointAlgebra(bC), IdentityMatrix(k,&+sorted_dims), start, d[i] );
      Append(~Flat_Bimaps1,temp1);
      Append(~Flat_Bimaps2,temp2);
    else //sloped 
		  Append(~TRX1, ExtractBlock(BB1[1], start, start + d[i] div 2, d[i] div 2, d[i] div 2) );
		  Append(~TRY1, ExtractBlock(BB1[2], start, start + d[i] div 2, d[i] div 2, d[i] div 2) );
		  Append(~TRX2, ExtractBlock(BB2[1], start, start + d[i] div 2, d[i] div 2, d[i] div 2) );
		  Append(~TRY2, ExtractBlock(BB2[2], start, start + d[i] div 2, d[i] div 2, d[i] div 2) );
    end if;
    start +:= d[i];
	end for;

	// We get the flat blocks into standard form using Pete's code.
	// We record the transformations with Ci.
  flatdim := &+(flats cat [0]);
	if flatdim gt 0 then
		C1 := DiagonalJoin( < __TransformFIPair( Bi ) : Bi in Flat_Bimaps1 > );
		C2 := DiagonalJoin( < __TransformFIPair( Bi ) : Bi in Flat_Bimaps2 > );
		C1 := DiagonalJoin( C1, IdentityMatrix( k, Dimension(bB`Domain[1]) - flatdim ) );
		C2 := DiagonalJoin( C2, IdentityMatrix( k, Dimension(bC`Domain[1]) - flatdim ) );
	else
		C1 := IdentityMatrix( k, Dimension(bB`Domain[1]) );
		C2 := C1;
	end if;

	// If it consists only of flat blocks, then they must be isomorphic.
	if sloped eq [] then
		Z := GL(2,k)!1;
		X := C2^(-1) * C1;
		// Sanity check!
		//if Sanity then
		//	LHS := [ X * BB1[1] * Transpose( X ), X * BB1[2] * Transpose( X ) ];
		//	RHS := [ &+[ Z[i][j]*SystemOfForms(bC)[j] : j in [1..2] ] : i in [1..2] ];
		//	assert LHS eq RHS;
		//end if;
		return true, [*X,Z*];
	end if;

	// Now we assume there exists at least one sloped block
	// There need not be any flat blocks

	// Put the blocks in the form [ I, C ] (or [ C, I ]), where C is a companion matrix
	// First we get it in the form [ I, * ]
	AinvBlocks1 := [**];
	AinvBlocks2 := [**];
	XTracker1 := [ 0 : i in [si..#d] ];
	XTracker2 := [ 0 : i in [si..#d] ];
	for i in [1..#TRX1] do
		if IsInvertible(TRX1[i]) then
			A1 := TRX1[i]^(-1);
		else
			A1 := TRY1[i]^(-1);
			XTracker1[i] := 1;
		end if;
		if IsInvertible(TRX2[i]) then
			A2 := TRX2[i]^(-1);
		else
			A2 := TRY2[i]^(-1);
			XTracker2[i] := 1;
		end if;
		Append(~AinvBlocks1,A1);
		TRX1[i] := A1*TRX1[i];
		TRY1[i] := A1*TRY1[i];
		Append(~AinvBlocks2,A2);
		TRX2[i] := A2*TRX2[i];
		TRY2[i] := A2*TRY2[i];
	end for;
	A1 := IdentityMatrix( k, flatdim );
	A2 := IdentityMatrix( k, flatdim );
	for i in [1..#AinvBlocks1] do
		A1 := DiagonalJoin( A1, DiagonalJoin( AinvBlocks1[i], IdentityMatrix( k, Ncols(AinvBlocks1[i]) ) ) );
		A2 := DiagonalJoin( A2, DiagonalJoin( AinvBlocks2[i], IdentityMatrix( k, Ncols(AinvBlocks1[i]) ) ) );
	end for;

	// Now we get the other matrix into rational canonical form
	QBlocks1 := [**];
	QBlocks2 := [**];
	for i in [1..#TRX1] do
		if XTracker1[i] eq 0 then
			RCF1, Q1 := RationalForm(TRY1[i]);
			TRY1[i] := RCF1;
		else
			RCF1, Q1 := RationalForm(TRX1[i]);
			TRX1[i] := RCF1;
		end if;
		Append(~QBlocks1, Q1);
		if XTracker2[i] eq 0 then
			RCF2, Q2 := RationalForm(TRY2[i]);
			TRY2[i] := RCF2;
		else
			RCF2, Q2 := RationalForm(TRX2[i]);
			TRX2[i] := RCF2;
		end if;
		Append(~QBlocks2, Q2);
	end for;
	Q1 := IdentityMatrix( k, flatdim );
	Q2 := IdentityMatrix( k, flatdim );
	for i in [1..#QBlocks1] do
		Q1 := DiagonalJoin( Q1, DiagonalJoin( QBlocks1[i], Transpose( QBlocks1[i]^(-1) ) ) );
		Q2 := DiagonalJoin( Q2, DiagonalJoin( QBlocks2[i], Transpose( QBlocks2[i]^(-1) ) ) );
	end for;

	// Associate indeterminants with each pair to obtain polynomials
	R := PolynomialRing(k,2);
	poly1 := [];
	poly2 := [];
	for i in [1..#TRX1] do
		Append(~poly1, Determinant( TRX1[i] * R.1 + TRY1[i] * R.2 ));
		Append(~poly2, Determinant( TRX2[i] * R.1 + TRY2[i] * R.2 ));
	end for;

	// Test each Z in PGL(2,k)
	//"Searching PGL(2,k)...";
  act := OrbitAction( GL(2,k), LineOrbits(GL(2,k))[1][1] ); // The action of GL on the line (1,0)
  Perms := Image( act ); // PGL(2,k)
	isit := exists(Z){ Z : Z in Perms |  
    {* __GL2ActionOnPolynomial( poly2[i], Z @@ act ) : i in [1..#poly2] *} eq {* poly1[i] : i in [1..#poly1] *} };
	if isit then
		Z := Z @@ act;
    poly2_Z := [ __GL2ActionOnPolynomial( poly2[i], Z ) : i in [1..#poly2] ];
		perm := __FindPermutation( poly1, poly2_Z );
		P := __PermutationDegreeMatrix( k, [ d[i] : i in [si..#d] ], perm );
		P := DiagonalJoin( IdentityMatrix( k, flatdim ), P );

		// Lift the flat parts
		if flatdim gt 0 then
			F := DiagonalJoin( < __LiftFlatGenus2( Z, d[i] ) : i in [1..#flats] > ); //lifts for flats
		else
			F := IdentityMatrix( k, 0 );
		end if;
		F := DiagonalJoin( F, IdentityMatrix( k, Dimension(bB`Domain[1]) - flatdim ) );

		// Lift the sloped parts
		M := IdentityMatrix( k, flatdim );
		for i in [1..#poly1] do
			Lift := __LiftSlopeGenus2( poly2[i], poly1[perm[i]], Z  : Sanity := Sanity );
			M := DiagonalJoin( M, DiagonalJoin( Transpose(Lift[1]), Lift[2] ) );
		end for;
		M := Transpose( M );
		X1 := M * F * Transpose( P ) * Q1 * A1 * C1;
		X2 := Q2 * A2 * C2; 
		X := X2^(-1) * X1;

		/*
				There are many matrices, each doing a different thing.
				C1 = Matrix to get flat into standard form (based on Pete's form)
				A1 = Matrix to turn invertibles into identity
				Q1 = Matrix to get the other one into RCF
				P = Permutation matrix to align the slopes
				F = Lifts of the flats
				M = Lifts of the slopes
		*/

		// Sanity check!
		//LHS := [ X * BB1[1] * Transpose( X ), X * BB1[2] * Transpose( X ) ];
		//RHS := [ &+[ Z[j][i]*SystemOfForms(bC)[j] : j in [1..2] ] : i in [1..2] ];
		//assert LHS eq RHS;

		return true,[*X,Z*];
	end if;

	return false,_;
end function;

__Pfaffian_AUT := function( sB, d : Sanity := false )
	k := BaseRing(sB);
  p := Characteristic(k);
  B := SystemOfForms(sB);
	// Now that the bimaps are in block diagonal form, we extract the top right corner
	TRX := [**];
	TRY := [**];
  start := 1;
	for i in [1..#d] do
		Append(~TRX, ExtractBlock(B[1], start, start + d[i] div 2, d[i] div 2, d[i] div 2) );
		Append(~TRY, ExtractBlock(B[2], start, start + d[i] div 2, d[i] div 2, d[i] div 2) );
    start +:= d[i];
	end for;

	// Put the blocks in the form [ I, C ] (or [ C, I ]), where C is a companion matrix
	// First we get it in the form [ I, * ]
	AinvBlocks := [**];
	XTracker := [ 0 : i in [1..#d] ];
	for i in [1..#d] do
		if IsInvertible(TRX[i]) then
			A := TRX[i]^(-1);
		else
			A := TRY[i]^(-1);
			XTracker[i] := 1;
		end if;
		Append(~AinvBlocks,A);
		TRX[i] := A*TRX[i];
		TRY[i] := A*TRY[i];
	end for;
	A := IdentityMatrix( k, 0 );
	for i in [1..#AinvBlocks] do
		A := DiagonalJoin( A, DiagonalJoin( AinvBlocks[i], IdentityMatrix( k, Ncols(AinvBlocks[i]) ) ) );
	end for;

	// Now we get the other matrix into rational canonical form
	QBlocks := [**];
	for i in [1..#d] do
		if XTracker[i] eq 0 then
			RCF, Q := RationalForm(TRY[i]);
			TRY[i] := RCF;
		else
			RCF, Q := RationalForm(TRX[i]);
			TRX[i] := RCF;
		end if;
		Append(~QBlocks, Q);
	end for;
	Q := IdentityMatrix( k, 0 );
	for i in [1..#QBlocks] do
		Q := DiagonalJoin( Q, DiagonalJoin( QBlocks[i], Transpose( QBlocks[i]^(-1) ) ) );
	end for;

	// Associate indeterminants with each pair to obtain polynomials
	R := PolynomialRing(k,2);
	poly1 := [ Determinant( TRX[i] * R.1 + TRY[i] * R.2 ) : i in [1..#d] ];
	poly2 := poly1;

  delete TRX, TRY, AinvBlocks, XTracker, QBlocks;

  //Needed for PGL
  cleartop := function( X, k )
    if X[1][1] ne 0 then
      X := X[1][1]^-1 * MatrixAlgebra( k, 2 )!X;
    else
      X := X[1][2]^-1 * MatrixAlgebra( k, 2 )!X;
    end if;
    return X;
  end function;
  act := OrbitAction( GL(2,k), LineOrbits(GL(2,k))[1][1] ); // The action GL on the line (1,0)
  Perms := Image( act ); // PGL(2,k)

	// Test each Z in PGammaL(2,k)
	inner := [];
  outer := [];
	boolval := false;
  for Z_perm in Perms do
	  Z := cleartop( Z_perm @@ act, k );
    if Z eq Parent(Z)!1 then
      Z := PrimitiveElement(k) * Z;
    end if;
    poly2_Z := [ __GL2ActionOnPolynomial( poly2[i], Z ) : i in [1..#poly2] ];
    mul_poly2 := {* poly2_Z[i] : i in [1..#poly2] *};
    mul_poly1 := {* poly1[i] : i in [1..#poly1] *};

    if mul_poly1 eq mul_poly2 then
	    boolval := true;
	    perm := __FindPermutation( poly1, poly2_Z );
	    P := __PermutationDegreeMatrix( k, [ d[i] : i in [1..#d] ], perm );

	    // Lift the sloped parts
	    M := IdentityMatrix( k, 0 );
	    for i in [1..#poly1] do
		    Lift := __LiftSlopeGenus2( poly2[i], poly1[perm[i]], Z  : Sanity := Sanity );
		    M := DiagonalJoin( M, DiagonalJoin( Transpose(Lift[1]), Lift[2] ) );
	    end for;
	    M := Transpose( M );
	    X2 := Q * A;
	    X1 := M * Transpose( P ) * X2; 
	    X := X2^(-1) * X1;

	    /*
			    There are many matrices, each doing a different thing.
			    P1 = Permutation matrix to sort the blocks by flat to slope
			    C1 = Matrix to get flat into standard form (based on Pete's
				      form)
			    A = Matrix to turn invertibles into identity
			    Q = Matrix to get the other one into RCF
			    P = Permutation matrix to align the slopes
			    F = Lifts of the flats
			    M = Lifts of the slopes
	    */

	    // Sanity check!
      //S := SystemOfForms(sB);
      //assert [ X*F*Transpose(X) : F in S ] eq [ &+[ Z[j][i]*S[j] : j in [1..#S] ] : i in [1..Nrows(Z)] ];
      Append( ~inner, X );
      Append( ~outer, Lift[3] );
    end if;
  end for;

	return inner, outer;
end function;
