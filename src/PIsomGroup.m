/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


import "GlobalVars.m" : __SANITY_CHECK;
import "Pfaffian.m" : __Pfaffian_AUT;
import "Util.m" : __FindPermutation, __PermutationDegreeMatrix, __GetStarAlg, __WhichMethod;
import "Flat.m" : __TransformFIPair, __LiftFlatGenus2;
import "sloped.m" : PseudoIsometryGroupAdjointTensor;


__G1_PIsometry := function( B : Print := false )
  k := BaseRing(B);
  Form := SystemOfForms(B);
  vprintf TameGenus, 1 : "Computing the isometry group... ";
  tt := Cputime();
  Isom := IsometryGroup( Form : DisplayStructure := false );
  timing := Cputime(tt);
  vprintf TameGenus, 1 : "%o seconds.\n", timing;

  // Sanity check
  if __SANITY_CHECK then
    for X in Generators(Isom) do
      _ := IsHomotopism(B, B, [* X, X, IdentityMatrix(k, 1) *]);
    end for;
  end if;

  prim := PrimitiveElement(k);
  pseudo_in := [X : X in Generators(Isom)] cat [prim*IdentityMatrix(k, Nrows(Form[1]))];
  pseudo_out := [IdentityMatrix(k, 1) : i in [1..Ngens(Isom)]] cat [DiagonalMatrix(k, [prim^2])];

  return pseudo_in, pseudo_out, FactoredOrder(Isom)*Factorization(#k - 1);
end function;


/*
This is the function which combines both Pete's and Josh's code into one function for automorphisms.

Method: if set to 0, it uses the established cut offs for determining which method to use.
	If set to 1, then we use the polynomial method, and if set to 2, we use the adjoint tensor method. 
*/

__G2_PIsometry := function( B : Method := 0 )
  k := BaseRing(B);

  /* Step 1: Compute the adjoint algebra of the forms. */
  vprintf TameGenus, 1 : "Computing the adjoint algebra...";
  tt := Cputime();
  A := AdjointAlgebra( B );
  timing := Cputime(tt);
  vprintf TameGenus, 1 : " %o seconds.\n", timing;

	/* Step 2: Get a perp-decomposition and organize blocks. */
  vprintf TameGenus, 1 : "Computing perp-decomposition...";
  tt := Cputime();
	T, dims := PerpDecomposition( B );
  timing := Cputime(tt);
  vprintf TameGenus, 1 : " %o seconds.\n", timing;
	F := [ T * X * Transpose( T ) : X in SystemOfForms(B) ];
  flatdims := [ d : d in dims | IsOdd(d) ];
  slopeddims := [ d : d in dims | IsEven(d) ];
  Sort(~flatdims);
  Sort(~slopeddims);
  dims_sorted := flatdims cat slopeddims;
  adjten := __WhichMethod(Method,#k,slopeddims);

  vprintf TameGenus, 1 : "%o sloped blocks and %o flat blocks.\nDims: %o\n", #slopeddims, #flatdims, dims_sorted;

  P := __PermutationDegreeMatrix( k, dims, __FindPermutation( dims_sorted, dims ) ); 
  F := [ P * F[i] * Transpose( P ) : i in [1..2] ];
  if flatdims eq [] then Append(~flatdims,0); end if;
  if slopeddims eq [] then Append(~slopeddims,0); end if;
  Flat := [ ExtractBlock( F[i], 1, 1, &+flatdims, &+flatdims ) : i in [1..2] ];
  if &+flatdims gt 0 then
    fB := Tensor( Flat, 2, 1 );
    fB`Adjoint := __GetStarAlg(A,P*T,1,&+flatdims);
  end if;
  Sloped := [ ExtractBlock( F[i], &+flatdims+ 1, &+flatdims + 1, &+slopeddims, &+slopeddims ) : i in [1..2] ];
  if &+slopeddims gt 0 then
    sB := Tensor( Sloped, 2, 1 );
    if adjten then
      sB`Adjoint := __GetStarAlg(A,P*T,1+&+flatdims,&+slopeddims);
    end if;
  end if;

  /* Step 3: Lift the sloped */
  if &+slopeddims gt 0 then
    // determine which method to use
    if adjten then
      // Adjoint-tensor method
      vprintf TameGenus, 1 : "Adjoint-tensor method...";
      tt := Cputime();
		  inner_s, outer := PseudoIsometryGroupAdjointTensor( sB );
      outer := [ Transpose(outer[k]) : k in [1..#outer] ];
    else
      // Pfaffian method
      vprintf TameGenus, 1 : "Pfaffian method...";
      tt := Cputime();
      inner_s, outer := __Pfaffian_AUT( sB, slopeddims );
    end if;
    pseudo_order := Factorization(#outer)*Factorization(#k - 1);
    timing := Cputime(tt);
    vprintf TameGenus, 1 : " %o seconds.\n", timing;
  else
    inner_s := [ IdentityMatrix( k, 0 ) : i in [1..2] ];
    outer := [ x : x in Generators( GL(2, k) ) ];
    pseudo_order := FactoredOrderGL(2, #k);
  end if;

	/* Step 4: Lift the flat blocks */
  if &+flatdims gt 0 then
    i := 1;
    S := IdentityMatrix( k, 0 );
    for d in flatdims do
      Flat1 := ExtractBlock( Flat[1], i, i, d, d );
      Flat2 := ExtractBlock( Flat[2], i, i, d, d );
      tempB := Tensor( [Flat1,Flat2], 2, 1 );
      tempB`Adjoint := __GetStarAlg( AdjointAlgebra(fB), IdentityMatrix(k,&+flatdims), i, d );
      S := DiagonalJoin( S, __TransformFIPair( tempB ) );
      i +:= d;
    end for;
    inner_f := [];
    for Z in outer do 
      X := IdentityMatrix( k, 0 );
      for d in flatdims do
        X := DiagonalJoin( X, __LiftFlatGenus2( Z, d ) );
      end for;
      Append( ~inner_f, S^-1 * X * S );
    end for;
  else
    inner_f := [ IdentityMatrix( k, 0 ) : i in [1..#outer] ];
  end if;
  inner := [ ( P * T )^-1 * DiagonalJoin( inner_f[i], inner_s[i] ) * P * T : i in [1..#outer] ];

  // Sanity check 
  if __SANITY_CHECK then
    for i in [1..#inner] do
      Forms := SystemOfForms(B);
      assert [ inner[i] * Forms[j] * Transpose( inner[i] ) : j in [1..2] ] eq [ &+[ outer[i][y][x]*Forms[y] : y in [1..2] ] : x in [1..2] ];
    end for; 
  end if;
	
	/* Step 5: Construct generators for isometry group */
  tt := Cputime();
  vprintf TameGenus, 1 : "Constructing the isometries...";
  isom := IsometryGroup( SystemOfForms(B) : DisplayStructure := false, Adjoint := A );
  timing := Cputime(tt);
  vprintf TameGenus, 1 : " %o seconds.\n", timing;
  isom_order := FactoredOrder(isom); // Isometry group already stores this.
  // Sanity
  for i in [1..Ngens(isom)] do
    Forms := SystemOfForms(B);
    assert [ isom.i * Forms[j] * Transpose( isom.i ) : j in [1..2] ] eq Forms;
  end for; 

  /* Step 6: Combine everything from steps 3 - 5. */
  pseudo_in := inner cat [ x : x in Generators(isom) ];
  pseudo_out := outer cat [ IdentityMatrix( k, 2 ) : i in [1..Ngens(isom)] ];
   

  // Sanity check
  if __SANITY_CHECK then
    for i in [1..#pseudo_in] do
      Forms := SystemOfForms(B);
      assert [ pseudo_in[i] * Forms[j] * Transpose( pseudo_in[i] ) : j in [1..2] ] eq 
          [ &+[ pseudo_out[i][y][x]*Forms[y] : y in [1..2] ] : x in [1..2] ];
    end for;
  end if;

  return pseudo_in, pseudo_out, isom_order*pseudo_order;
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic TGPseudoIsometryGroup( B::TenSpcElt : Cent := true, Method := 0 ) -> GrpMat
{Construct the pseudo-isometry group for an alternating bimap of genus 1 or 2. 
To use a specific method for genus 2, set Method to 1 for adjoint-tensor method or 2 for Pfaffian method.}
  require forall{ X : X in Frame(B) | Type(X) eq ModTupFld } : "Domain and codomain must be vector spaces.";
  require B`Valence eq 3 : "Tensor must have valence 3.";
  require IsAlternating(B) : "Tensor must be alternating.";
  k := BaseRing(B);
  require ISA(Type(k),FldFin) : "Base ring must be a finite field.";
  require Characteristic(k) ne 2 : "Must be odd characteristic.";

  // remove the radical.
  vprintf TameGenus, 1 : "Removing the radical... ";
  tt := Cputime();
  Rad := Radical(B, 2);
  Forms := SystemOfForms(B);
  if Dimension(Rad) gt 0 then
    C := Complement(Generic(Rad), Rad);
    RadPerm := GL(Dimension(B`Domain[1]), k)!Matrix(Basis(C) cat Basis(Rad));
    nForms := [ RadPerm*X*Transpose(RadPerm) : X in Forms ];
    nForms := [ ExtractBlock(X, 1, 1, Ncols(Forms[1])-Dimension(Rad), Ncols(Forms[1])-Dimension(Rad)) : X in nForms ];  
    nB := Tensor( nForms, 2, 1 );
  else
    nForms := Forms;
    nB := B;
  end if; 
  timing := Cputime(tt);
  vprintf TameGenus, 1 : "%o seconds.\n", timing;

  // write bimap over its centroid. 
  if Cent then
    vprintf TameGenus, 1 : "Rewriting tensor over its centroid... ";
    tt := Cputime();
    T, H := TensorOverCentroid(nB);
    vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);
  else
    T := nB;
  end if;
  require Dimension(T`Codomain) le 2 : "Tensor is not genus 1 or 2.";

  // if genus 1, do a simpler algorithm.
  if Dimension(T`Codomain) eq 1 then
    IN, OUT, ORD := __G1_PIsometry(T);
  else
    // if Cent is not prime field, do adj-ten method.
    if not IsPrimeField(BaseRing(T)) then
      Method := 1; 
      vprintf TameGenus, 1 : "Centroid is not a prime field, applying adjoint-tensor method.\n";
    end if;
    IN, OUT, ORD := __G2_PIsometry( T : Method := Method );
  end if;

  vprintf TameGenus, 1 : "Putting everything together... ";
  tt := Cputime();

  // check if non-trivial centroid.
  if BaseRing(T) ne BaseRing(B) then
    "WARNING: Full pseudo-isometry group has not been constructed.  The centroid is a proper field extension, so there are potential Galois actions missing.";
    V := Domain(H.2);
    IN := [ Matrix([ Eltseq(((V.i@H.2)*X)@@H.2) : i in [1..Dimension(V)] ]) : X in IN ];
    W := Domain(H.0);
    OUT := [ Matrix([ Eltseq(((W.i@H.0)*X)@@H.0) : i in [1..Dimension(W)] ]) : X in OUT ]; 
  end if;

  // add pseudo-isometries on radical.
  if Dimension(Rad) gt 0 then
    Radgens := [ DiagonalJoin(IdentityMatrix(k, Ncols(nForms[1])), x) : x in Generators(GL(Dimension(Rad), k)) ];
    Radcentrals := [];
    for i in [1..Ncols(nForms[1])] do
      for j in [1..Dimension(Rad)] do
        X := IdentityMatrix( k, Ncols(nForms[1]) + Dimension(Rad) );
        X[i][Ncols(nForms[1])+j] := 1;
        Append(~Radcentrals, X);
      end for;
    end for;
    pseudo_in := [ DiagonalJoin( X, IdentityMatrix( k, Dimension(Rad) ) ) : X in IN ] cat Radgens cat Radcentrals;
    pseudo_in := [ RadPerm^-1 * pseudo_in[i] * RadPerm : i in [1..#pseudo_in] ];
    pseudo_out := OUT cat [ IdentityMatrix( k, #Forms ) : i in [1..#Radgens+#Radcentrals] ];
    ORD *:= FactoredOrderGL(Dimension(Rad), #k);
    ORD *:= FactoredOrder(#k)^(Dimension(C)*Dimension(Rad));
  else
    pseudo_in := IN;
    pseudo_out := OUT;
  end if;

  // Sanity check
  if __SANITY_CHECK then
    for i in [1..#pseudo_in] do
      _ := IsHomotopism(B, B, [* pseudo_in[i], pseudo_in[i], pseudo_out[i] *]);
    end for;
  end if;

  PIsom := sub< GL( Ncols(Forms[1])+#Forms, k ) | [ DiagonalJoin( pseudo_in[i], pseudo_out[i] ) : i in [1..#pseudo_in] ] >;
  DerivedFrom(~PIsom, B, {0..2}, {0, 2});
  PIsom`FactoredOrder := ORD;
  PIsom`Order := Integers()!ORD;
  timing := Cputime(tt);
  vprintf TameGenus, 1 : "%o seconds.\n", timing;

  return PIsom;
end intrinsic;
