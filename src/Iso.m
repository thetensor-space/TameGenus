/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "GlobalVars.m" : __SANITY_CHECK;
import "Util.m" : __GL2ActionOnPolynomial, __GetStarAlg, __WhichMethod,
    __Print_field, __Radical_removal, __Display_adj_info, __Get_Flat_and_Sloped,
    __MyIDMatrix, __Basic_invariant_check, __Transform_Adjoint;
import "Pfaffian.m" : __Pfaffian_ISO;
import "sloped.m" : IsPseudoIsometricAdjointTensor;
import "LiftFlat.m" : __LiftFlatGenus2;
import "flat.m" : __TransformFIPair;
import "Semilinear.m" : __Standard_Gen, __Galois_Cent;


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

// Assumes X and Y are alternating, in block diagonal form, with 2x2 blocks.
__Interweave_units := function(X, Y)
  d := Nrows(X);
  assert d eq Nrows(Y);
  units := &cat[[X[2*(k-1)+1][2*k]^-1, Y[2*(k-1)+1][2*k]] : k in [1..d div 2]];
  return DiagonalMatrix(units);
end function;

__G1_Isotopism := function(s, t : Const := true)
  vprintf TameGenus, 1 : "\nGenus 1 case.\n";
  K := BaseRing(s);
  A_s := AdjointAlgebra(s);
  A_t := AdjointAlgebra(t);

  if Const then

    // We know that there are no radicals, and conjugating by T puts it into 
    // block diagonal form, where the blocks are 2x2. 
    _, s_b, H_s := __Get_Flat_and_Sloped(s);
    _, t_b, H_t := __Get_Flat_and_Sloped(t);
    D := __Interweave_units(SystemOfForms(s_b)[1], SystemOfForms(t_b)[1]);

    X := < (H_t.2)^-1 * D * H_s.2, IdentityMatrix(K, 1) >;

    // Sanity check
    if __SANITY_CHECK then
      assert IsHomotopism(t, s, [*X[1], X[1], X[2]*]);
    end if;

    return true, X; 
  end if;

  return true, _;
end function;

__IsPseudoSG := function( s, t : Constructive := true, Method := 0 )
  K := BaseRing(s);

  vprintf TameGenus, 1 : "\nComputing the adjoint algebra.\n";
  tt := Cputime();

  A_s := AdjointAlgebra(s);
  A_t := AdjointAlgebra(t);

  vprintf TameGenus, 2 : "Adjoint construction timing : %o s.\n", Cputime(tt);

  // genus 1
  if Dimension(Codomain(s)) eq 1 then
    return __G1_Isotopism(s, t : Const := Constructive);
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
  if #sdims_s eq 0 then
    adjten := false;
  else
    adjten := __WhichMethod(Method, #K, sdims_s);
  end if;
  
  s_block := Codomain(H_s);
  t_block := Codomain(H_t);
  s_block`Bimap`Adjoint := __Transform_Adjoint(A_s, H_s.2);
  t_block`Bimap`Adjoint := __Transform_Adjoint(A_t, H_t.2);
  // There is a simplification here, but I don't know what StarAlge needs.
  //assert AdjointAlgebra(s_block) eq sub<Generic(A_s) | [H_s.2 * X * (H_s.2)^-1 :
  //    X in Generators(A_s)]>;
  //assert AdjointAlgebra(t_block) eq sub<Generic(A_t) | [H_t.2 * X * (H_t.2)^-1 :
  //    X in Generators(A_t)]>;
  
  tt := Cputime();

  if adjten then
    check_pisom, X := __IsPseudoSGAdjTens(s_sloped, t_sloped);
    if check_pisom then
      X := [* X[1], Transpose(X[2]) *]; // fixes a transpose issue with adj-tens
    end if;
    method := "Adjoint-tensor";
  else
    check_pisom, X := __IsPseudoSGPfaffian(fdims_s, sdims_s, s_block, t_block : 
        Constructive := Constructive );
    method := "Pfaffian";
  end if;

  if #sdims_s gt 0 then
    vprintf TameGenus, 2 : "%o method timing : %o s\n", method, Cputime(tt);
  else
    vprintf TameGenus, 2 : "Lifting flats timing : %o s\n", Cputime(tt);
  end if;

  if not Constructive or not check_pisom then
    return check_pisom, _; 
  end if;

  X[1] := (H_t.2)^-1 * X[1] * H_s.2;

  // sanity check
  if __SANITY_CHECK then
    assert IsHomotopism(t, s, [*X[1], X[1], X[2]*], HomotopismCategory(3));
  end if;

  return true, <X[1], X[2]>;
end function;



__Galois_wrapped_IsPseudo := function(F, G : Const := true, Method := 0)
  s := Domain(F);
  S := Codomain(F);
  t := Domain(G);
  T := Codomain(G);
  V := Domain(t)[1];
  W := Codomain(t);
  
  // Compute the adjoint algebras
  vprintf TameGenus, 1 : "\nComputing the adjoint algebra.\n";
  tt := Cputime();

  A_s := AdjointAlgebra(S);
  A_t := AdjointAlgebra(T);
  __Display_adj_info(A_s : subscript := "_s");
  __Display_adj_info(A_t : subscript := "_t");

  vprintf TameGenus, 2 : "Adjoint construction timing : %o s.\n", Cputime(tt);

  // Quick adjoint check
  if Multiset(SimpleParameters(A_s)) ne Multiset(SimpleParameters(A_t)) then
    vprintf TameGenus, 1 : "\nAdjoint algebras are not isomorphic.\n";
    return false, _;
  end if;


  if #BaseRing(S) ne #BaseRing(s) then

    // There are potential isomorphisms arising from Galois actions
    vprintf TameGenus, 1 : "\nPotential Galois actions present.\n";

    // First construct a homotopism that mimics Galois
    Y := __Standard_Gen(G);
    Z := __Galois_Cent(Y);
    dims := [Dimension(X) : X in Frame(t)];
    Z2 := ExtractBlock(Z, 1, 1, dims[1], dims[1]);
    Z0 := ExtractBlock(Z, dims[1] + 1, dims[1] + 1, dims[3], dims[3]);
    Cat := TensorCategory([-1, -1, 1], {{0}, {1, 2}});
    Z_a := func< a | Homotopism([*Z2^-a, Z2^-a, Z0^a*], Cat) >;

    // Because we haven't changed the centroid of t by applying Z_a, we can use
    // the same given homotopism.
    G_a := Homotopism([*G.2^-1, G.1^-1, G.0*], Cat);

    // Now, we loop until either we have an isomorphism or we run out of Galois
    check_pseudo_isom := false;
    a := -1;
    while (not check_pseudo_isom) and (a lt Degree(BaseRing(S), BaseRing(s))) do
      a +:= 1;
      T_a := t @ Z_a(a) @ G_a;
      // Throw the adjoint algebra back on 
      if a eq 0 then
        T_a`Bimap`Adjoint := A_t;
      end if;
      check_pseudo_isom, X := __IsPseudoSG(S, T_a : Constructive := Const, 
          Method := Method);
    end while;

    // update the homotopism to account for the homotopism Z_a
    if check_pseudo_isom then
      Hmt_Z := Homotopism(t, t @ Z_a(a), [*Z2^a, Z2^a, Z0^a*], 
          HomotopismCategory(3) : Check := __SANITY_CHECK);
    else 
      Hmt_Z := Homotopism(t, t, [*__MyIDMatrix(X) : X in Frame(t)*], 
          HomotopismCategory(3) : Check := false);
    end if;

  else

    // No Galois, run like normal.
    check_pseudo_isom, X := __IsPseudoSG(S, T : Constructive := Const, 
        Method := Method);
    Hmt_Z := Homotopism(t, t, [*__MyIDMatrix(X) : X in Frame(t)*], 
          HomotopismCategory(3) : Check := false);

  end if;

  // Build the isotopism if we need to
  if Const and check_pseudo_isom then
    Y := [**];
    // if the centroid is an extension convert back
    if #BaseRing(s) ne #BaseRing(S) then
      Y[1] := Matrix([((V.i @ Hmt_Z.2 @ G.2)*X[1]) @@ F.2 : 
          i in [1..Dimension(V)]]);
      Y[2] := Matrix([((W.i @ Hmt_Z.0 @ G.0)*X[2]) @@ F.0 : 
          i in [1..Dimension(W)]]);
    else
      Y := [*X[1], X[2]*];
    end if;

    H := Homotopism(s, t, [*Y[1], Y[1], Y[2]*] : Check := __SANITY_CHECK); 

    return true, H;
  end if;

  return check_pseudo_isom, _;
end function;


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic TGIsPseudoIsometric( s::TenSpcElt, t::TenSpcElt : Cent := true, 
    Constructive := true, Method := 0 ) -> BoolElt, Hmtp
{Determine if two alternating tame genus 3-tensors are pseudo-isometric over a 
finite field of odd characteristic.}
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

  // Check radical dimensions
  if dim_rad_s ne dim_rad_t or dim_crad_s ne dim_crad_t then
    vprintf TameGenus, 1 : "\nRadicals have different dimensions.\n";
    return false, _;
  end if;

  // Check the frames
  if Frame(s_nondeg) ne Frame(t_nondeg) then
    vprintf TameGenus, 1 : "\nTensors have non-equivalent frames.\n";
    return false, _;
  end if;

  // Once we have a radical wrapper, we can remove this requirement
  require forall{X : X in Frame(t_nondeg) | Dimension(X) gt 0} : 
      "Cannot handle tensors with 0-dimensional vector spaces.";

  // JBW centroid work around.----------------------
  // TensorOverCentroid only works over fields right now.
  // so check.
  pi, C0 := Induce(Centroid(s_nondeg),0);
  pi, D0 := Induce(Centroid(t_nondeg),0);
  if Cent and IsSimple(C0) and IsSimple(D0) then
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
    S := s_nondeg;
    Hmt_S := Homotopism(S, S, [*__MyIDMatrix(X) : X in Frame(S)*]);
    T := t_nondeg;
    Hmt_T := Homotopism(T, T, [*__MyIDMatrix(X) : X in Frame(T)*]);

  end if;

  // Check that their centroids are isomorphic
  if #BaseRing(S) ne #BaseRing(T) then
    vprint TameGenus, 1 : "\nCentroids are not isormorphic.";
    return false, _;
  end if;

  require Dimension(Codomain(S)) le 2 : "Tensors have genus greater than 2.";


  is_iso, H := __Galois_wrapped_IsPseudo(Hmt_S, Hmt_T : Const := Constructive, 
      Method := Method);

  if is_iso and dim_rad_s gt 0 then
    X := DiagonalJoin(H.2, IdentityMatrix(BaseRing(S), dim_rad_s));
    return true, Homotopism(s, t, [*Z_t^-1*X*Z_s, Z_t^-1*X*Z_s, H.0*]);
  else
    // H will not be defined if is_iso is false.
    if is_iso then
      return is_iso, H;
    else
      return is_iso, _;
    end if;
  end if;
end intrinsic;


intrinsic TGIsIsomorphic( G::GrpPC, H::GrpPC : Cent := true, 
    Constructive := true, Method := 0 ) -> BoolElt, Map
{For genus 2 p-groups G and H, determine if G is isomorphic to H.}
  // Rule out easy pairs
  check_basics := __Basic_invariant_check(G, H);
  if not check_basics then
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
    vprintf TameGenus, 1 : 
        "Groups are abelian. Using Magma's default algorithm.";
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

  check_pseudo_isom, Hmt := TGIsPseudoIsometric(s, t : Cent := Cent, 
      Constructive := Constructive, Method := Method);

  if Constructive then
    if check_pseudo_isom then
      V := Codomain(maps_H[1]);
      G_gens := [G.i : i in [1..Ngens(G)]];
      X := Hmt.2;
      im := [(V!((x @ phi_G @ maps_G[1])*X)) @@ maps_H[1] @@ phi_H : x in G_gens];
      
      phi := hom< G -> H | [<G_gens[i], im[i]> : i in [1..#im]] : 
          Check := __SANITY_CHECK >;

      return true, phi;
    else
      return false, _;
    end if;
  end if;

  return check_pseudo_isom, _;
end intrinsic;
