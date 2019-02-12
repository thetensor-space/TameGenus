/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "GlobalVars.m" : __SANITY_CHECK;
import "Util.m" : __GL2ActionOnPolynomial, __GetStarAlg, __WhichMethod,
    __Print_field, __Radical_removal, __Display_adj_info, __Get_Flat_and_Sloped;
import "Pfaffian.m" : __Pfaffian_ISO;
import "sloped.m" : IsPseudoIsometricAdjointTensor;
import "LiftFlat.m" : __LiftFlatGenus2;
import "flat.m" : __TransformFIPair;

__GetIdempotents := function( A )
  n := Nrows(A.1);
  return [ A.2^-i*A.1*A.2^i : i in [0..n-1] ];
end function;

__IsPseudoSGPfaffian := function( flats, sloped, bB, bC : Constructive := true )
  if Constructive then
    check_pisom, pi := __Pfaffian_ISO(bB, bC, flats, sloped);
    if not check_pisom then
      return false, _;
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
    // The action of GL on the line (1,0)
    act := OrbitAction( GL(2,k), LineOrbits(GL(2,k))[1][1] ); 
    Perms := Image( act ); // PGL(2,k)
    return exists{ X : X in Perms | polys1 eq {* R!(__GL2ActionOnPolynomial( f, 
        X @@ act )) : f in polys2 *} }, _;
  end if;
end function;

__IsPseudoSGAdjTens := function( sB, sC )
  isit, X, Z := IsPseudoIsometricAdjointTensor( sB, sC );
  if not isit then 
    return false, _;
  end if;
  return isit, [*X, Z*];
end function;

__IsPseudoSG := function( F, G : Constructive := true, Method := 0 )
  s := Codomain(F);
  t := Codomain(G);
  K := BaseRing(s);

  vprintf TameGenus, 1 : "\nComputing the adjoint algebra.\n";
  tt := Cputime();

  A_s := AdjointAlgebra(s);
  A_t := AdjointAlgebra(t);
  __Display_adj_info(A_s : subscript := "_s");
  __Display_adj_info(A_t : subscript := "_t");

  vprintf TameGenus, 2 : "Adjoint construction timing : %o s.\n", Cputime(tt);

  // Quick adjoint check
  if SimpleParameters(A_s) ne SimpleParameters(A_t) then
    vprintf TameGenus, 1 : "\nAdjoint algebras are not isomorphic.\n";
    return false, _;
  end if;

  // genus 1
  if Dimension(Codomain(s)) eq 1 then
    vprintf TameGenus, 1 : "\nGenus 1 case.\n";
    if Constructive then

      // Hack until bug in StarAlg gets fixed for forms.
      I1 := __GetIdempotents(A_s);
      I2 := __GetIdempotents(A_t);
      S1 := Matrix( &cat[ Basis( Image( I1[i] ) ) : i in [1..#I1] ] );
      S2 := Matrix( &cat[ Basis( Image( I2[i] ) ) : i in [1..#I2] ] );
      bForms1 := [ S1*SystemOfForms(s)[1]*Transpose(S1) ];
      bForms2 := [ S2*SystemOfForms(t)[1]*Transpose(S2) ];
      N1 := ExtractBlock( bForms1[1], 1, Nrows(bForms1[1]) div 2 + 1, 
          Nrows(bForms1[1]) div 2, Nrows(bForms1[1]) div 2 );
      N2 := ExtractBlock( bForms2[1], 1, Nrows(bForms1[1]) div 2 + 1, 
          Nrows(bForms1[1]) div 2, Nrows(bForms1[1]) div 2 );
      T := DiagonalJoin( N2 * N1^-1, IdentityMatrix( K, Nrows(N1) ) );
      X := < S2^-1 * T * S1, IdentityMatrix(K, 1) >;

      // Sanity check
      if __SANITY_CHECK then
        assert IsHomotopism(s, t, [*X[1], X[1], X[2]*]);
      end if;

      return true, DiagonalJoin(X); 
    else
      return true, _;
    end if;
  end if;

  // genus 2
  vprintf TameGenus, 1 : "\nGenus 2 case.\n";
  vprintf TameGenus, 1 : 
      "\nDecomposing tensors into flat and sloped subtensors.\n";
  tt := Cputime(); 

  s_flat, s_sloped, H_s, fdims_s, sdims_s := __Get_Flat_and_Sloped(s);
  t_flat, t_sloped, H_t, fdims_t, sdims_t := __Get_Flat_and_Sloped(t);

  // Quick checks
  if (fdims_s ne fdims_t) or (sdims_s ne sdims_t) then
    vprint TameGenus, 1 : "\nGenus 2 signatures are not the same.";
    return false, _; 
  end if;
  if not Constructive and (sdims_s eq []) then 
    return true, _; 
  end if;

  vprintf TameGenus, 1 : "\tBlock dims = %o\n", fdims_s cat sdims_s;
  vprintf TameGenus, 2 : "Perp-decomposition timing : %o s\n", Cputime(tt);


  // if it's just flat, go to the Pfaffian function.
  if sdims_s eq [] then
    adjten := false;
  else
    adjten := __WhichMethod(Method, #K, sdims_s);
  end if;
  
  s_block := Codomain(H_s);
  t_block := Codomain(H_t);
  assert AdjointAlgebra(s_block) eq sub<Generic(A_s) | [H_s.2 * X * (H_s.2)^-1 :
      X in Generators(A_s)]>;
  assert AdjointAlgebra(t_block) eq sub<Generic(A_t) | [H_t.2 * X * (H_t.2)^-1 :
      X in Generators(A_t)]>;

  if adjten then
    vprintf TameGenus, 1 : "Using adjoint-tensor method... ";
    tt := Cputime();
    check_pisom, X := __IsPseudoSGAdjTens(s_sloped, t_sloped);
    if check_pisom then
      X := [* X[1], Transpose(X[2]) *]; // fixes a transpose issue with adj-tens
    end if;
  else
    vprintf TameGenus, 1 : "Using Pfaffian method... ";
    tt := Cputime();
    check_pisom, X := __IsPseudoSGPfaffian(fdims_s, sdims_s, s_block, t_block : 
        Constructive := Constructive );
  end if;
  vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);

  if not Constructive or not check_pisom then
    return check_pisom, _; 
  end if;

  X[1] := (H_t.2)^-1 * X[1] * H_s.2;

  // sanity check
  if __SANITY_CHECK then
    assert [ X[1] * F * Transpose(X[1]) : F in SystemOfForms(s) ] eq 
        [ &+[ X[2][j][i]*SystemOfForms(t)[j] : j in [1..2] ] : i in [1..2] ];
  end if;

  return true, <X[1], X[2]>;
end function;


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic TGIsPseudoIsometric( s::TenSpcElt, t::TenSpcElt : Cent := true, 
    Constructive := true, Method := 0 ) -> BoolElt, Hmtp
{Determine if two genus 2 alternating tensors are pseudo-isometric over a finite 
field of odd characteristic.}
  K := BaseRing(s);
  L := BaseRing(t);
  require ISA(Type(K), FldFin) and ISA(Type(L), FldFin) : 
    "Base rings must be finite fields.";
  require #K eq #L : "Base rings must be the same.";
  require Valence(s) eq 3 and Valence(t) eq 3 : "Tensors must have valence 3.";
  require Characteristic(K) ne 2 : "Characteristic must be odd.";
  require IsAlternating(s) and IsAlternating(t) : 
      "Tensors must be alternating.";
  require Type(Cent) eq BoolElt : "'Cent' must be true or false.";
  require Type(Constructive) eq BoolElt : 
      "'Constructive' must be true or false.";
  require Type(Method) eq RngIntElt : 
      "'Method' must be an integer in {0, 1, 2}.";


  s_nondeg, dim_rad_s, dim_crad_s, Z_s := __Radical_removal(s);
  t_nondeg, dim_rad_t, dim_crad_t, Z_t := __Radical_removal(t);


  if Cent then
    // write tensors over their centroids.
    vprintf TameGenus, 1 : "\nWriting tensors over their centroids.\n";
    tt := Cputime();

    S, Hmt_S := TensorOverCentroid(s_nondeg);
    T, Hmt_T := TensorOverCentroid(t_nondeg);

    __Print_field(S, "s");
    __Print_field(T, "t");
    vprintf TameGenus, 2 : "Writing over centroid timing : %o s\n", Cputime(tt);

  else

    // Skip the centroid step.
    vprintf TameGenus, 1 : "\nCent turned OFF.\n";
    S := s;
    Hmt_S := Homotopism(S, S, [*Hom(X, X)!1 : X in Frame(S)*]);
    T := t;
    Hmt_T := Homotopism(T, T, [*Hom(X, X)!1 : X in Frame(T)*]);

  end if;

  // Check obvious things
  if #BaseRing(S) ne #BaseRing(T) then
    vprint TameGenus, 1 : "Centroids are not isormorphic.";
    return false, _;
  end if;
  if (Dimension(Domain(S)[1]) ne Dimension(Domain(T)[1])) or 
      (Dimension(Codomain(S)) ne Dimension(Codomain(T))) then
    vprint TameGenus, 1 : "Domains or codomains not isormorphic.";
    return false, _;
  end if;

  require Dimension(Codomain(S)) le 2 : "Tensors have genus greater than 2.";

  check_pseudo_isom, X := __IsPseudoSG(Hmt_S, Hmt_T : 
      Constructive := Constructive, Method := Method);

  /*if Constructive and check_pseudo_isom then
    vprintf TameGenus, 1 : "Putting everything together... ";
    tt := Cputime();

    // if the centroid is an extension of the prime field convert back to prime field
    if Cent and (#BaseRing(s) ne #BaseRing(S)) then
      V := Domain(Domain(Hmt_T))[1];
      W := Codomain(Domain(Hmt_T));
      Y1 := Matrix([ ((V.i @ Hmt_T.2)*X[1])@@Hmt_S.2 : i in [1..Dimension(V)] ]);
      Y2 := Matrix([ ((W.i @ Hmt_T.0)*X[2])@@Hmt_S.0 : i in [1..Dimension(W)] ]);
    else
      V := Domain(s)[1];
      W := Codomain(s);
    end if;
    H := Homotopism(s, t, [*X[1], X[1], X[2]*]); // check built in
    vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);
    return true, H;
  end if;*/

  return check_pseudo_isom, _;
end intrinsic;


intrinsic TGIsIsomorphic( G::GrpPC, H::GrpPC : Cent := true, 
    Constructive := true, Method := 0 ) -> BoolElt
{For genus 2 p-groups G and H, determine if G is isomorphic to H.}
  // Rule out easy pairs
  if (Exponent(G) ne Exponent(H)) or (#G ne #H) or 
      (NilpotencyClass(G) ne NilpotencyClass(H)) then
    return false, _;
  end if;

  require IsPrime(Exponent(G)) : "Groups do not have exponent p.";
  require NilpotencyClass(G) le 2 : "Groups are not class 2.";
  require IsOdd(#G) : "Groups must have odd order.";
  require Type(Cent) eq BoolElt : "'Cent' must be true or false.";
  require Type(Constructive) eq BoolElt : 
      "'Constructive' must be true or false.";
  require Type(Method) eq RngIntElt : 
      "'Method' must be an integer in {0, 1, 2}.";

  // Abelian case
  if IsAbelian(G) then 
    return IsIsomorphic(G, H);
  end if;

  // To smooth things out
  P, phi_G := pQuotient(G, Exponent(G), 2 : Print := 0);
  Q, phi_H := pQuotient(H, Exponent(H), 2 : Print := 0);
  
  // Construct the p-central tensors and move to the tensor call.
  vprintf TameGenus, 1 : 
      "Extracting p-central tensors and deciding pseudo-isometry.\n";
	t, maps_G := pCentralTensor(P, 1, 1);
  s, maps_H := pCentralTensor(Q, 1, 1);
  _ := Eltseq(t);
  _ := Eltseq(s);
  t`Reflexive`Alternating := true;
  t`Reflexive`Antisymmetric := true;
  s`Reflexive`Alternating := true;
  s`Reflexive`Antisymmetric := true;

  check_pseudo_isom, Hmt := TGIsPseudoIsometric(t, s : Cent := Cent, 
      Constructive := Constructive, Method := Method);

  if Constructive then
    if check_pseudo_isom then
      V := Codomain(maps_H[1]);
      G_gens := [G.i : i in [1..Dimension(V)]];
      X := Hmt`Maps[1]; 
      //phi := [<G.i, ((G.i @ G_maps[1])*(Hmt`Maps[1])) @@ H_maps[1]> : i in [1..Nrows(Hmt`Maps[1])]];
      //return true, hom< G -> H | phi >;
      im := [(V!((x @ phi_G @ maps_G[1])*X)) @@ maps_H[1] @@ phi_H : x in G_gens];
      
      if __SANITY_CHECK then
        phi := hom< G -> H | [<G_gens[i], im[i]> : i in [1..#im]] >;
      else
        phi := hom< G -> H | [<G_gens[i], im[i]> : i in [1..#im]] : Check := false >;
      end if;

      return true, phi;
    else
      return false, _;
    end if;
  end if;

  return check_pseudo_isom, _;
end intrinsic;
