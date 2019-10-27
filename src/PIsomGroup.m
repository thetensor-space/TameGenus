/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "GlobalVars.m" : __SANITY_CHECK;
import "Pfaffian.m" : __Pfaffian_AUT;
import "Util.m" : __FindPermutation, __PermutationDegreeMatrix, __GetStarAlg, 
    __WhichMethod, __SmallerGenSet, __Get_Flat_and_Sloped, __Display_order, 
    __Print_field, __Radical_removal, __Display_adj_info;
import "Flat.m" : __TransformFIPair, __LiftFlatGenus2;
import "sloped.m" : PseudoIsometryGroupAdjointTensor;
import "Iso.m" : __IsPseudoSG;
import "Semilinear.m" : __RewriteMat, __Galois_check;


__Radical_auts := function(K, d_nd, d_rad)
  Radgens := [DiagonalJoin(IdentityMatrix(K, d_nd), x) : 
      x in Generators(GL(d_rad, K))];
  Radcentrals := [];
  for i in [1..d_nd] do
    for j in [1..d_rad] do
      X := IdentityMatrix(K, d_nd + d_rad);
      X[i][d_nd + j] := 1;
      Append(~Radcentrals, X);
    end for;
  end for;
  return Radgens cat Radcentrals;
end function;


__G1_PIsometry := function( t, H : Print := false )
  K := BaseRing(t);

  // Construct generators for isometry group
  vprintf TameGenus, 1 : "\nConstructing the pseudo-isometry group.\n";
  tt := Cputime();

  pisom := SimilarityGroup(SystemOfForms(t)[1]);

  pisom_order := FactoredOrder(IsometryGroup(SystemOfForms(t) : 
      DisplayStructure := false)) * Factorization(#K-1); 
  vprintf TameGenus, 2 : "\tPseudo-isometry order : %o\n", 
      __Display_order(pisom_order);
  vprintf TameGenus, 2 : "Pseudo0isometry construction timing : %o s\n", Cputime(tt);


  // Use InducePseudoIsometry to get the action of pisom on the 0 coordinate.
  pseudo_in := [Matrix(X) : X in Generators(pisom)];
  pseudo_out := [];
  for X in pseudo_in do
    F := Homotopism([*X, X, 0*], HomotopismCategory(3));
    check_lift, G := InduceHomotopism(t, t, F, 0);
    assert check_lift;
    Append(~pseudo_out, Matrix(G.0));
  end for;

  
  // Check if there are non-trivial Galois actions
  if #BaseRing(Domain(H)) ne #K then

    vprintf TameGenus, 1 : "\nChecking Galois automorphisms.\n";

    pseudo_in := [__RewriteMat(X, H.2) : X in pseudo_in];
    pseudo_out := [__RewriteMat(X, H.0) : X in pseudo_out];
    galois_in, galois_out, galois_ord := __Galois_check(H);
    pseudo_in cat:= galois_in;
    pseudo_out cat:= galois_out;

    vprintf TameGenus, 2 : "\tGalois order : %o\n", 
        __Display_order(galois_ord);

  else

    galois_ord := Factorization(1); // hilarious...

  end if;


  // Sanity check
  if __SANITY_CHECK then
    vprintf TameGenus, 1 : "\nRunning sanity check.\n";
    tt := Cputime();
    s := Domain(H);
    assert forall{i : i in [1..#pseudo_in] | IsHomotopism(s, s, [*pseudo_in[i],
        pseudo_in[i], pseudo_out[i]*], HomotopismCategory(3))};
    vprintf TameGenus, 2 : "Sanity test timing : %o s\n", Cputime(tt);
  end if;


  return pseudo_in, pseudo_out, pisom_order * galois_ord;
end function;


/*
  This is the function which combines both Pete's and Josh's code into one 
  function for automorphisms.

  Input: a tensor over its centroid and a homotopism H with image t. 

  Method: if set to 0, it uses the established cut offs for determining which 
  method to use. If set to 1, then we use the polynomial method, and if set to 
  2, we use the adjoint tensor method. 
*/

__G2_PIsometry := function( t, H : Method := 0 )

  k := BaseRing(t);

  // Step 1: Compute the adjoint algebra of the forms.
  vprintf TameGenus, 1 : "\nComputing the adjoint algebra.\n";
  tt := Cputime();

  A := AdjointAlgebra(t);
  __Display_adj_info(A);

  vprintf TameGenus, 2 : "Adjoint construction timing : %o s.\n", Cputime(tt);

  // Break off the flat and sloped subtensors of t 
  vprintf TameGenus, 1 : 
      "\nDecomposing tensor into flat and sloped subtensors.\n";
  tt := Cputime(); 

  t_flat, t_slope, F, f_dims, s_dims := __Get_Flat_and_Sloped(t);

  vprintf TameGenus, 1 : "\tBlock dims = %o\n", f_dims cat s_dims;
  vprintf TameGenus, 2 : "Perp-decomposition timing : %o s\n", Cputime(tt);


  // Step 3: Lift the sloped
  vprintf TameGenus, 1 : "\nNumber of sloped blocks to lift: %o.\n", #s_dims;
  if #s_dims gt 0 then

    // determine which method to use
    adjten := __WhichMethod(Method, #k, s_dims);
    tt := Cputime();

    if adjten then

      // Adjoint-tensor method
		  inner_s, outer := PseudoIsometryGroupAdjointTensor(t_slope);
      // Requires this little transpose fix
      outer := [Transpose(outer[k]) : k in [1..#outer]];
      method := "Adjoint-tensor";

    else

      // Pfaffian method
      inner_s, outer := __Pfaffian_AUT(t_slope, s_dims);
      method := "Pfaffian";

    end if;

    // Maybe I could dig and figure this out, but it's just in a GL2.
    // Seems like LMG might handle it just fine. 
    // We can come back if we need. --JM (30.01.2019)
    inner_s, outer, pseudo_order := __SmallerGenSet(inner_s, outer);

  else

    inner_s := [IdentityMatrix( k, 0 ) : i in [1..2]];
    outer := [x : x in Generators(GL(2, k))];
    pseudo_order := FactoredOrderGL(2, #k);

  end if;


  vprintf TameGenus, 1 : "\nNumber of flat blocks to lift: %o.\n", #f_dims;
	// Step 4: Lift the flat blocks
  if #f_dims gt 0 then

    // In this case, there is a non-trivial flat block
    i := 1;
    S := IdentityMatrix(k, 0);
    Flat := SystemOfForms(t_flat);

    // We decompose Flat (the flat system of forms) into indecomposable forms. 
    for d in f_dims do
      Flat_ind := [ExtractBlock(Flat[j], i, i, d, d) : j in [1..2]];
      flat_ind_t := Tensor(Flat_ind, 2, 1);
      S := DiagonalJoin(S, __TransformFIPair(flat_ind_t));
      i +:= d;
    end for;

    inner_f := [];

    // Run through all the Z in GL(2, k) that induce a pseudo-isometry, and lift
    // them to the flat part. 
    for Z in outer do 
      X := IdentityMatrix(k, 0);
      for d in f_dims do
        X := DiagonalJoin(X, __LiftFlatGenus2(Z, d));
      end for;
      // The corresponding lift of Z on the flat part.
      Append(~inner_f, S^-1 * X * S);
    end for;

  else

    // In this case, there are no flat indecomposables.
    inner_f := [ IdentityMatrix( k, 0 ) : i in [1..#outer] ];

  end if;

  // Since we transformed our original bimap by F.2, we undo that here on the 
  // inner part. (The outer part was the identity.)
  inner := [(F.2)^-1 * DiagonalJoin(inner_f[i], inner_s[i]) * F.2 : 
      i in [1..#outer]];

  vprintf TameGenus, 2 : "\tPseudo-isometry order : %o\n", 
      __Display_order(pseudo_order);
  if #s_dims gt 0 then
    vprintf TameGenus, 2 : "%o method timing : %o s\n", method, Cputime(tt);
  else
    vprintf TameGenus, 2 : "Lifting flats timing : %o s\n", Cputime(tt);
  end if;


  // Sanity check 
  if __SANITY_CHECK then
    vprintf TameGenus, 1 : "\nRunning sanity check.\n";
    tt := Cputime();
    assert forall{i : i in [1..#inner] | IsHomotopism(t, t, [*inner[i], 
        inner[i], outer[i]*], HomotopismCategory(3))};
    vprintf TameGenus, 2 : "Sanity test timing : %o s\n", Cputime(tt);
  end if;
	

	// Construct generators for isometry group
  vprintf TameGenus, 1 : "\nConstructing the isometry group.\n";
  tt := Cputime();

  if GetVerbose("TameGenus") eq 0 then
    disp := false;
  else
    disp := true;
  end if;
  isom := IsometryGroup(SystemOfForms(t) : DisplayStructure := disp, 
      Adjoint := A);

  isom_order := FactoredOrder(isom); // Isometry group already stores this.
  vprintf TameGenus, 2 : "\tIsometry order : %o\n", 
      __Display_order(isom_order);
  vprintf TameGenus, 2 : "Isometry construction timing : %o s\n", Cputime(tt);


  // Sanity check on isometry group
  if __SANITY_CHECK then
    vprintf TameGenus, 1 : "\nRunning sanity check.\n";
    tt := Cputime();
    I2 := IdentityMatrix(k, 2);
    assert forall{I : I in Generators(isom) | IsHomotopism(t, t, [*I, I, 
        I2*], HomotopismCategory(3))};
    vprintf TameGenus, 2 : "Sanity test timing : %o s\n", Cputime(tt);
  end if;


  // Combine everything from steps 3 - 5.
  pseudo_in := inner cat [Matrix(x) : x in Generators(isom)];
  pseudo_out := outer cat [IdentityMatrix( k, 2 ) : i in [1..Ngens(isom)]];


  // Check if there are non-trivial Galois actions
  if #BaseRing(Domain(H)) ne #BaseRing(t) then

    vprintf TameGenus, 1 : "\nChecking Galois automorphisms.\n";

    pseudo_in := [__RewriteMat(X, H.2) : X in pseudo_in];
    pseudo_out := [__RewriteMat(X, H.0) : X in pseudo_out];
    galois_in, galois_out, galois_ord := __Galois_check(H);
    pseudo_in cat:= galois_in;
    pseudo_out cat:= galois_out;

    vprintf TameGenus, 2 : "\tGalois order : %o\n", __Display_order(galois_ord);

  else

    galois_ord := Factorization(1); // hilarious...

  end if;


  // Sanity check
  if __SANITY_CHECK then
    vprintf TameGenus, 1 : "\nRunning sanity check.\n";
    tt := Cputime();
    s := Domain(H);
    assert forall{i : i in [1..#pseudo_in] | IsHomotopism(s, s, [*pseudo_in[i],
        pseudo_in[i], pseudo_out[i]*], HomotopismCategory(3))};
    vprintf TameGenus, 2 : "Sanity test timing : %o s\n", Cputime(tt);
  end if;


  return pseudo_in, pseudo_out, isom_order * pseudo_order * galois_ord;
end function;


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic TGPseudoIsometryGroup( t::TenSpcElt : Cent := true, Method := 0 ) -> 
    GrpMat
{Construct the pseudo-isometry group for an alternating bimap of genus 1 or 2. 
To use a specific method for genus 2, set Method to 1 for adjoint-tensor method 
or 2 for Pfaffian method.}
  require forall{X : X in Frame(t) | Type(X) eq ModTupFld} : 
      "Domain and codomain must be vector spaces.";
  require Valence(t) eq 3 : "Tensor must have valence 3.";
  require IsAlternating(t) : "Tensor must be alternating.";
  K := BaseRing(t);
  require ISA(Type(K), FldFin) : "Base ring must be a finite field.";
  p := Characteristic(K);
  require p ne 2 : "Must be odd characteristic.";

  /*
    The code in this part of the intrinsic does a few things:
      1. remove the radicals,
      2. write the tensor over its centroid,
      3. export the fully nondegenerate tensor to get pseudo-isomtry group,
      4. add in any pseudo-isomtries from the radicals,
      5. add bookkeeping attributes to the pseudo-isometry group. 
  */

  // Remove the radicals
  t_fn, d_rad, d_crad, Z1, Z2 := __Radical_removal(t);

  // Once we have a radical wrapper, we can remove this requirement
  require forall{X : X in Frame(t_fn) | Dimension(X) gt 0} : 
     "Cannot handle tensors with 0-dimensional vector spaces.";

  // TensorOverCentroid only implemented for fields.
  pi, C0 := Induce(Centroid(t_fn), 0);
  if Cent and IsSimple(C0) then
    // Write tensor over its centroid. 
    vprintf TameGenus, 1 : "\nWriting tensor over its centroid.\n";
    tt := Cputime();
    T, H := TensorOverCentroid(t_fn);
    __Print_field(T, "t");
    vprintf TameGenus, 2 : "Writing over centroid timing : %o s\n", Cputime(tt);
  else
    // Skip the centroid step.
    vprintf TameGenus, 1 : "\nEither Cent turned off or centroid not simple.\n";
    T := t_fn;
    dims_T := [Dimension(X) : X in Frame(T)];
    H := Homotopism(T, T, [*IdentityMatrix(K, dims_T[1]), 
        IdentityMatrix(K, dims_T[2]), IdentityMatrix(K, dims_T[3])*]);
  end if;


  // Check genus <= 2.
  if Cent and not IsSimple(C0) then
    require Dimension(Codomain(T)) le 2 : "Centroid is not a field. Algorithm only implemented for centroids that are fields.";
  else
    require Dimension(Codomain(T)) le 2 : "Tensor is not genus 1 or 2.";
  end if;


  // Construct pseudo-isometry group
  if Dimension(Codomain(T)) eq 1 then
  
    vprintf TameGenus, 1 : "\nTensor has genus 1.\n";
    IN, OUT, ORD := __G1_PIsometry(T, H);

  else

    vprintf TameGenus, 1 : "\nTensor has genus 2.\n";
    IN, OUT, ORD := __G2_PIsometry(T, H : Method := Method);

  end if;

  dims_t_fn := [Dimension(X) : X in Frame(t_fn)];
  if d_rad gt 0 then
    // Add pseudo-isometries on radical.
    vprintf TameGenus, 1 : "\nIncluding the pseudo-isometries from the radical.\n";
  
    rad_auts := __Radical_auts(K, dims_t_fn[1], d_rad);
    pseudo_in := [DiagonalJoin(X, IdentityMatrix(K, d_rad)) : X in IN] cat 
        rad_auts;
    pseudo_in := [Z1^-1 * pseudo_in[i] * Z1 : i in [1..#pseudo_in]];
    pseudo_out := OUT cat [IdentityMatrix(K, dims_t_fn[3]) : 
        i in [1..#rad_auts]];
    ORD *:= FactoredOrderGL(d_rad, #K);
    ORD *:= Factorization(#K)^(dims_t_fn[1]*d_rad); // Doublecheck
  else
    pseudo_in := IN;
    pseudo_out := OUT;
  end if;

  if d_crad gt 0 then
    // Add pseudo-isometries on co-radical.
    vprintf TameGenus, 1 : "\nIncluding the pseudo-isometries from the co-radical.\n";

    crad_auts := [Transpose(X) : X in __Radical_auts(K, dims_t_fn[3], d_crad)];
    pseudo_in cat:= [IdentityMatrix(K, dims_t_fn[1] + d_rad) : 
        i in [1..#crad_auts]];
    pseudo_out := [DiagonalJoin(X, IdentityMatrix(K, d_crad)) : X in pseudo_out]
        cat crad_auts;
    pseudo_out := [Z2 * X * Z2^-1 : X in pseudo_out];
    ORD *:= FactoredOrderGL(d_crad, #K);
    ORD *:= Factorization(#K)^(dims_t_fn[3]*d_crad);
  end if;


  // Sanity check
  if __SANITY_CHECK then
    vprintf TameGenus, 1 : "\nRunning sanity check.\n";
    tt := Cputime();
    assert forall{i : i in [1..#pseudo_in] | IsHomotopism(t, t, [*pseudo_in[i],
        pseudo_in[i], pseudo_out[i]*], HomotopismCategory(3))};
    vprintf TameGenus, 2 : "Sanity test timing : %o s\n", Cputime(tt);
  end if;


  // Put the group together
  PIsom := sub< GL(Dimension(Domain(t)[1]) + Dimension(Codomain(t)), K) | 
      [DiagonalJoin(pseudo_in[i], pseudo_out[i]) : i in [1..#pseudo_in]] >;
  // Give it some useful attributes
  DerivedFrom(~PIsom, t, {0..2}, {0, 2});
  PIsom`FactoredOrder := ORD;
  PIsom`Order := Integers()!ORD;


  return PIsom;
end intrinsic;
