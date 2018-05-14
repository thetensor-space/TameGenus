/* 
    Copyright 2015--2017, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


import "Util.m" : __GL2ActionOnPolynomial, __PermutationDegreeMatrix, __FindPermutation, __GetStarAlg, __WhichMethod, __WriteMatrixOverPrimeField;
import "Pfaffian.m" : __Pfaffian_ISO;
import "sloped.m" : IsPseudoIsometricAdjointTensor;
import "LiftFlat.m" : __LiftFlatGenus2;
import "flat.m" : __TransformFIPair;

__GetIdempotents := function( A )
  n := Nrows(A.1);
  return [ A.2^-i*A.1*A.2^i : i in [0..n-1] ];
end function;

__IsPseudoSGPfaffian := function( flats, sloped, bB, bC : Constructive := false )
  if Constructive then
    isit, pi := __Pfaffian_ISO( bB, bC, flats, sloped : Sanity := true );
    if not isit then
      return false,_;
    else
      return true, pi;
    end if;
  else
    bForms1 := SystemOfForms(bB);
    bForms2 := SystemOfForms(bC);
    k := BaseRing(bForms1[1]);
    R := PolynomialRing( k, 2 );
    start := &+(flats cat [0]) + 1;
    polys1 := {**};
    polys2 := {**};
    for d in sloped do
      X := ExtractBlock( bForms1[1], start, start + d div 2, d div 2, d div 2);
      Y := ExtractBlock( bForms1[2], start, start + d div 2, d div 2, d div 2);
      det := Determinant( X*R.1 + Y*R.2 );
      Include(~polys1, Coefficients(det)[1]^-1 * det );
      X := ExtractBlock( bForms2[1], start, start + d div 2, d div 2, d div 2);
      Y := ExtractBlock( bForms2[2], start, start + d div 2, d div 2, d div 2);
      det := Determinant( X*R.1 + Y*R.2 );
      Include(~polys2, Coefficients(det)[1]^-1 * det );
      start +:= d;
    end for;
    act := OrbitAction( GL(2,k), LineOrbits(GL(2,k))[1][1] ); // The action of GL on the line (1,0)
    Perms := Image( act ); // PGL(2,k)
    return exists{ X : X in Perms | polys1 eq {* R!(__GL2ActionOnPolynomial( f, X @@ act )) : f in polys2 *} }, _;
  end if;
end function;

__IsPseudoSGAdjTens := function( flats, sloped, bB, bC )
  pos := &+(flats cat [0]) + 1;
  s := &+(sloped cat [0]);
  K := BaseRing(bB);
  sForms1 := [ ExtractBlock(F,pos,pos,s,s) : F in SystemOfForms(bB) ];
  sForms2 := [ ExtractBlock(F,pos,pos,s,s) : F in SystemOfForms(bC) ];
  sB := Tensor( sForms1, 2, 1 );
  sB`Adjoint := __GetStarAlg( AdjointAlgebra(bB), IdentityMatrix(K,pos+s-1), pos, s );
  sC := Tensor( sForms2, 2, 1 );
  sC`Adjoint := __GetStarAlg( AdjointAlgebra(bC), IdentityMatrix(K,pos+s-1), pos, s );
  isit,X,Z := IsPseudoIsometricAdjointTensor( sB, sC );
  if not isit then 
    return false,_;
  end if;
  return isit,[*X,Z*];
end function;

__IsPseudoSG := function( B, C : Constructive := false, Method := 0, Print := false )
  k := BaseRing(B);
  // Peel off the radicals
  vprintf TameGenus, 1 : "Computing radicals... ";
  tt := Cputime();
  R1 := Radical(B,1);
  R2 := Radical(C,1);
  vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);
  if Dimension(R1) ne Dimension(R2) then
    return false,_;
  end if;
  if Dimension(R1) gt 0 then
    V := Generic(R1);
    C1 := Complement( V, R1 );
    C2 := Complement( V, R2 );
    M1 := Matrix( Basis( C1 ) cat Basis( R1 ) );
    M2 := Matrix( Basis( C2 ) cat Basis( R2 ) );
    nForms1 := [ ExtractBlock( M1*F*Transpose(M1), 1, 1, Nrows(M1)-Dimension(R1), Nrows(M1)-Dimension(R1) ) : F in SystemOfForms(B) ];
    nForms2 := [ ExtractBlock( M2*F*Transpose(M2), 1, 1, Nrows(M1)-Dimension(R1), Nrows(M1)-Dimension(R1) ) : F in SystemOfForms(C) ];
    nB := Tensor( nForms1, 2, 1 );
    nC := Tensor( nForms2, 2, 1 );
  else
    M1 := IdentityMatrix( k, Dimension(B`Domain[1]) );
    M2 := M1;
    nB := B;
    nC := C;
    nForms1 := SystemOfForms(nB);
    nForms2 := SystemOfForms(nC);
  end if;

  // trivial case -- genus 1
  if Dimension(B`Codomain) eq 1 then
    vprintf TameGenus, 1 : "Genus 1 case.\n";
    if Constructive then
      /* Hack until bug in StarAlg gets fixed for forms. */
      vprintf TameGenus, 1 : "Computing adjoint algebras... ";
      tt := Cputime();
      A1 := AdjointAlgebra( nB );
      A2 := AdjointAlgebra( nC );
      vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);
      I1 := __GetIdempotents( A1 );
      I2 := __GetIdempotents( A2 );
      S1 := Matrix( &cat[ Basis( Image( I1[i] ) ) : i in [1..#I1] ] );
      S2 := Matrix( &cat[ Basis( Image( I2[i] ) ) : i in [1..#I2] ] );
      bForms1 := [ S1*nForms1[1]*Transpose(S1) ];
      bForms2 := [ S2*nForms2[1]*Transpose(S2) ];
      N1 := ExtractBlock( bForms1[1], 1, Nrows(bForms1[1]) div 2 + 1, Nrows(bForms1[1]) div 2, Nrows(bForms1[1]) div 2 );
      N2 := ExtractBlock( bForms2[1], 1, Nrows(bForms1[1]) div 2 + 1, Nrows(bForms1[1]) div 2, Nrows(bForms1[1]) div 2 );
      T := DiagonalJoin( DiagonalJoin( N2 * N1^-1, IdentityMatrix( k, Nrows(N1) ) ), IdentityMatrix(k, Dimension(R1)) );
      S2 := DiagonalJoin( S2, IdentityMatrix(k,Dimension(R1)) );
      S1 := DiagonalJoin( S1, IdentityMatrix(k,Dimension(R1)) );
      X := < M2^-1 * S2^-1 * T * S1 * M1, IdentityMatrix(k,1) >;

      // Sanity check
      //assert [ X[1] * F * Transpose(X[1]) : F in SystemOfForms(B) ] eq SystemOfForms(B);
      return true, DiagonalJoin(X); 
    else
      return true,_;
    end if;
  end if;

  // genus 2
  vprintf TameGenus, 1 : "Genus 2 case.\n";
  vprintf TameGenus, 1 : "Computing adjoint algebras... ";
  tt := Cputime();
  A1 := AdjointAlgebra( nB );
  A2 := AdjointAlgebra( nC );
  vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);
  vprintf TameGenus, 1 : "Computing perp decompositions... ";
  tt := Cputime();
  T1,dims1 := PerpDecomposition( nB );
  T2,dims2 := PerpDecomposition( nC );
  vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);
  if Multiset(dims1) ne Multiset(dims2) then
    vprint TameGenus, 1 : "Genus 2 signatures are not the same.";
    return false,_; 
  end if;
  flats := Sort( [ d : d in dims1 | IsOdd(d) ] );
  sloped := Sort( [ d : d in dims1 | IsEven(d) ] );
  sorted_dims := flats cat sloped;
  adjten := __WhichMethod(Method,#k,sloped);
  vprintf TameGenus, 1 : "%o sloped blocks and %o flat blocks.\nDims: %o\n", #sloped, #flats, sorted_dims;
  //Sprintf( "%o sloped blocks and %o flat blocks.\nDims: %o", #sloped, #flats, sorted_dims );
  if not Constructive and sloped eq [] then 
    return true,_; 
  end if;
  P1 := __PermutationDegreeMatrix( k, dims1, __FindPermutation( sorted_dims, dims1 ) );
  bForms1 := [ P1*T1*F*Transpose(P1*T1) : F in SystemOfForms(nB) ];
  P2 := __PermutationDegreeMatrix( k, dims2, __FindPermutation( sorted_dims, dims2 ) );
  bForms2 := [ P2*T2*F*Transpose(P2*T2) : F in SystemOfForms(nC) ];

  // If it's sloped but the span of the forms is not 2 dimensional use Pfaffian regardless.
  // This is because Pete's code is built on the assumption that the span of the forms is 2 dimensional.
  if adjten then
    start := &+(flats cat [1]);
    d_s := &+(sloped cat [0]);
    S11 := ExtractBlock( bForms1[1], start, start, d_s, d_s ); 
    S12 := ExtractBlock( bForms1[2], start, start, d_s, d_s ); 
    S21 := ExtractBlock( bForms2[1], start, start, d_s, d_s ); 
    S22 := ExtractBlock( bForms2[2], start, start, d_s, d_s ); 
    S1 := sub< KMatrixSpace(k,d_s,d_s) | S11, S12 >;
    S2 := sub< KMatrixSpace(k,d_s,d_s) | S21, S22 >;
    if (Dimension(S1) ne 2) or (Dimension(S2) ne 2) then
      adjten := false;
    end if;
  end if;

  // if it's just flat, go to the Pfaffian function.
  if sloped eq [] then
    adjten := false;
  end if;

  bB := Tensor( bForms1, 2, 1 );
  bC := Tensor( bForms2, 2, 1 );
  if adjten or (#flats gt 0) then
    bB`Adjoint := __GetStarAlg( A1, P1*T1, 1, Nrows(bForms1[1]) );
    bC`Adjoint := __GetStarAlg( A2, P2*T2, 1, Nrows(bForms2[1]) );
  end if;

  if adjten then
    vprintf TameGenus, 1 : "Using adjoint-tensor method... ";
    tt := Cputime();
    isit,X := __IsPseudoSGAdjTens( flats, sloped, bB, bC );
    if isit then
      X := [* X[1], Transpose(X[2]) *]; // fixes a transpose issue with adj-tens
    end if;
  else
    vprintf TameGenus, 1 : "Using Pfaffian method... ";
    tt := Cputime();
    isit,X := __IsPseudoSGPfaffian( flats, sloped, bB, bC : Constructive := Constructive );
  end if;
  vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);

  if (not Constructive) or (not isit) then
    return isit,_; 
  end if;

  X[1] := M2^-1 * DiagonalJoin( T2^-1 * P2^-1 * X[1] * P1 * T1, IdentityMatrix(k, Dimension(R1) ) ) * M1;

  // sanity check
  assert [ X[1] * F * Transpose(X[1]) : F in SystemOfForms(B) ] eq [ &+[ X[2][j][i]*SystemOfForms(C)[j] : j in [1..2] ] : i in [1..2] ];
  return true, DiagonalJoin(X[1],X[2]);
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic TGIsPseudoIsometric( B::TenSpcElt, C::TenSpcElt : Cent := true, Constructive := true, Method := 0 ) -> BoolElt
{Determine if two genus 2 bimaps are pseduo-isometric.}
  k := BaseRing(B);
  l := BaseRing(C);
  require ISA(Type(k),FldFin) and ISA(Type(l),FldFin) : "Base rings must be finite fields.";
  require #k eq #l : "Base rings must be the same.";
  require B`Valence eq 3 and C`Valence eq 3 : "Tensors must be bimaps.";
  require forall{ X : X in Frame(B) cat Frame(C) | Type(X) eq ModTupFld } : 
    "Domains and codomains must be vector spaces.";
  require IsAlternating(B) and IsAlternating(C) : "Tensors must be alternating.";
  require Characteristic(k) ne 2 : "Characteristic must be odd.";
  require Type(Cent) eq BoolElt : "`Cent' must be true or false.";
  require Type(Constructive) eq BoolElt : "`Constructive' must be true or false.";
  require Type(Method) eq RngIntElt : "`Method' must be an integer in {0, 1, 2}.";

  try
    _ := Eltseq(B);
    _ := Eltseq(C);
  catch err
    error "Cannot compute structure constants.";
  end try;

  // write bimaps over their centroids.
  if Cent then
    vprintf TameGenus, 1 : "Rewriting tensors over their centroid... ";
    tt := Cputime();
    T, Hmt_T := TensorOverCentroid(B);
    S, Hmt_S := TensorOverCentroid(C);
    vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);
  else
    T := B;
    S := C;
  end if;

  // check obvious things.
  if BaseRing(T) ne BaseRing(S) then
    vprint TameGenus, 1 : "Base rings are not isormorphic.";
    return false,_;
  end if;
  if Dimension(T`Domain[1]) ne Dimension(S`Domain[1]) or Dimension(T`Codomain) ne Dimension(S`Codomain) then
    vprint TameGenus, 1 : "Domains or codomains not isormorphic.";
    return false,_;
  end if;

  require Dimension(T`Codomain) le 2 : "Tensors have genus greater than 2.";

  // if Cent is not prime field, do adj-ten method.
  if not IsPrimeField(BaseRing(T)) then
    Method := 1; 
    vprintf TameGenus, 1 : "Centroid is not a prime field, applying adjoint-tensor method.\n";
  end if;

  isit, X := __IsPseudoSG( T, S : Constructive := Constructive, Method := Method, Print := Print );

  if Constructive and isit then
    vprintf TameGenus, 1 : "Putting everything together... ";
    tt := Cputime();
    Y := [* ExtractBlock(X,1,1,Dimension(T`Domain[1]),Dimension(T`Domain[1])), 
      ExtractBlock(X,1+Dimension(T`Domain[1]),1+Dimension(T`Domain[1]),Dimension(T`Codomain),Dimension(T`Codomain)) *];
    assert [ Y[1] * F * Transpose(Y[1]) : F in SystemOfForms(T) ] eq [ &+[ Y[2][j][i]*SystemOfForms(S)[j] : j in [1..2] ] : i in [1..2] ];

    // if the centroid is an extension of the prime field convert back to prime field
    if Cent and not IsPrimeField(BaseRing(Y[1])) then
      V := Domain(Domain(Hmt_T))[1];
      W := Codomain(Domain(Hmt_T));
      Y1 := Matrix([ ((V.i @ Hmt_T.2)*Y[1])@@Hmt_S.2 : i in [1..Dimension(V)] ])^-1;
      Y2 := Matrix([ ((W.i @ Hmt_T.0)*Y[2])@@Hmt_S.0 : i in [1..Dimension(W)] ])^-1;
    else
      V := Domain(B)[1];
      W := Codomain(B);
      Y1 := Y[1]^-1;
      Y2 := Y[2]^-1;
    end if;
    H := Homotopism( B, C, [* Hom(V,V)!Y1, Hom(V,V)!Y1, Hom(W,W)!Y2 *] );
    vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);
    return true, H;
  end if;

  return isit,_;
end intrinsic;


intrinsic TGIsIsomorphic( G::GrpPC, H::GrpPC : Cent := true, Constructive := true, Method := 0 ) -> BoolElt
{For genus 2 p-groups G and H, determine if G is isomorphic to H.}
  if (Exponent(G) ne Exponent(H)) or (#G ne #H) or (NilpotencyClass(G) ne NilpotencyClass(H)) then
    return false,_;
  end if;
  require IsPrime(Exponent(G)) : "Groups do not have exponent p.";
  require NilpotencyClass(G) le 2 : "Groups are not class 2.";
  require IsOdd(#G) : "Groups must have odd order.";
  require Type(Cent) eq BoolElt : "`Cent' must be true or false.";
  require Type(Constructive) eq BoolElt : "`Constructive' must be true or false.";
  require Type(Method) eq RngIntElt : "`Method' must be an integer in {0, 1, 2}.";

  // Abelian case
  if IsAbelian(G) then 
    return IsIsomorphic(G, H);
  end if;
  
  // compute the system of forms.
  vprintf TameGenus, 1 : "Getting tensor info... ";
  tt := Cputime();
	t, G_maps := pCentralTensor(G);
  s, H_maps := pCentralTensor(H);
  _ := Eltseq(t);
  _ := Eltseq(s);
  vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);

  isit, Hmt := TGIsPseudoIsometric(t, s : Cent := Cent, Constructive := Constructive, Method := Method);

  if Constructive then
    if isit then
      phi := [<G.i, ((G.i @ G_maps[1])*(Hmt`Maps[1])) @@ H_maps[1]> : i in [1..Nrows(Hmt`Maps[1])]];
      return true, hom< G -> H | phi >;
    else
      return false, _;
    end if;
  else
    return isit, _;
  end if;  
end intrinsic;
