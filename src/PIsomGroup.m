/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "GlobalVars.m" : __SANITY_CHECK;
import "Pfaffian.m" : __Pfaffian_AUT;
import "Util.m" : __FindPermutation, __PermutationDegreeMatrix, __GetStarAlg, 
    __WhichMethod, __SmallerGenSet, __Galois_Cent, __RewriteMat, __Galois_Tango,
    __Get_Flat_and_Sloped;
import "Flat.m" : __TransformFIPair, __LiftFlatGenus2;
import "sloped.m" : PseudoIsometryGroupAdjointTensor;
import "Iso.m" : __IsPseudoSG;


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

Input: a tensor over its centroid and a homotopism H with image t. 

Method: if set to 0, it uses the established cut offs for determining which method to use.
	If set to 1, then we use the polynomial method, and if set to 2, we use the adjoint tensor method. 
*/

__G2_PIsometry := function( t, H : Method := 0 )

  k := BaseRing(t);

  // Step 1: Compute the adjoint algebra of the forms.
  vprintf TameGenus, 1 : "Computing the adjoint algebra...";
  tt := Cputime();
  A := AdjointAlgebra(t);
  timing := Cputime(tt);
  vprintf TameGenus, 1 : " %o seconds.\n", timing;

  // Break off the flat and sloped subtensors of t 
  vprintf TameGenus, 1 : "Computing perp-decomposition...";
  tt := Cputime(); 
  t_flat, t_slope, F, f_dims, s_dims := __Get_Flat_and_Sloped(t);
  timing := Cputime(tt);
  vprintf TameGenus, 1 : " %o seconds.\n", timing;


  vprintf TameGenus, 1 : "%o sloped blocks and %o flat blocks.\nDims: %o\n", 
      #s_dims, #f_dims, s_dims cat f_dims;


  // Step 3: Lift the sloped
  if #s_dims gt 0 then

    // determine which method to use
    adjten := __WhichMethod(Method, #k, s_dims);
    tt := Cputime();

    if adjten then

      // Adjoint-tensor method
      vprintf TameGenus, 1 : "Adjoint-tensor method...";
		  inner_s, outer := PseudoIsometryGroupAdjointTensor(t_slope);
      // Requires this little transpose fix
      outer := [Transpose(outer[k]) : k in [1..#outer]];

    else

      // Pfaffian method
      vprintf TameGenus, 1 : "Pfaffian method...";
      inner_s, outer := __Pfaffian_AUT(t_slope, s_dims);

    end if;

    // Maybe I could dig and figure this out, but it's just in a GL2.
    // Seems like LMG might handle it just fine. 
    // We can come back if we need. --JM (30.01.2019)
    inner_s, outer, pseudo_order := __SmallerGenSet(inner_s, outer);
    //assert pseudo_order eq LMGFactoredOrder(sub<GL(2, k) | outer>);
    timing := Cputime(tt);
    vprintf TameGenus, 1 : " %o seconds.\n", timing;

  else

    inner_s := [IdentityMatrix( k, 0 ) : i in [1..2]];
    outer := [x : x in Generators(GL(2, k))];
    pseudo_order := FactoredOrderGL(2, #k);

  end if;


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
      for d in flatdims do
        X := DiagonalJoin(X, __LiftFlatGenus2(Z, d));
      end for;
      // The corresponding lift of Z on the flat part.
      Append(~inner_f, S^-1 * X * S);
    end for;

  else

    // In this case, there are no flat indecomposables.
    inner_f := [ IdentityMatrix( k, 0 ) : i in [1..#outer] ];

  end if;

  // Since we transformed our original bimap by P*T, we undo that here on the 
  // inner part. (The outer part was the identity.)
  inner := [(P*T)^-1*DiagonalJoin(inner_f[i], inner_s[i])*P*T : 
      i in [1..#outer]];


  // Sanity check 
  if __SANITY_CHECK then
    assert forall{i : i in [1..#inner] | IsHomotopism(t, t, [*inner[i], 
        inner[i], outer[i]*], HomotopismCategory(3))};
  end if;
	

	// Step 5: Construct generators for isometry group
  tt := Cputime();
  vprintf TameGenus, 1 : "Constructing the isometries...";
  // Maybe eventually this will take a tensor instead of [Mtrx]
  isom := IsometryGroup(SystemOfForms(t) : DisplayStructure := false, 
      Adjoint := A);
  timing := Cputime(tt);
  vprintf TameGenus, 1 : " %o seconds.\n", timing;
  isom_order := FactoredOrder(isom); // Isometry group already stores this.
  //assert isom_order eq LMGFactoredOrder(sub< Generic(isom) | Generators(isom) >);

  // Sanity check on isometry group
  if __SANITY_CHECK then
    I2 := IdentityMatrix(k, 2);
    assert forall{I : I in Generators(isom) | IsHomotopism(t, t, [*I, I, 
        I2*], HomotopismCategory(3))};
  end if;

  // Step 6: Combine everything from steps 3 - 5.
  pseudo_in := inner cat [x : x in Generators(isom)];
  pseudo_out := outer cat [IdentityMatrix( k, 2 ) : i in [1..Ngens(isom)]];
   

  // Sanity check
  if __SANITY_CHECK then
    assert forall{i : i in [1..#pseudo_in] | IsHomotopism(t, t, [*pseudo_in[i],
        pseudo_in[i], pseudo_out[i]*], HomotopismCategory(3))};
  end if;

  // Step 3: check if non-trivial centroid.
  E := BaseRing(t);
  s := Domain(H);
  K := BaseRing(s);
  if #E ne #K then

    // Therefore, H is a nontrivial homotopism from s to t. 

    // Check which Galois automorphisms lift.
    Cent := Centroid(s);
    X := __Galois_Cent(Cent);
    Gal := sub< GL(Nrows(X), BaseRing(X)) | X >;
    Gal`FactoredOrder := FactoredOrder(X);
    Gal`Order := IntegerRing()!LMGFactoredOrder(Gal);
    DerivedFrom(~Gal, s, {0..2}, {0, 2});
    //assert forall{C : C in Generators(Cent) | X^-1*C*X in Cent};
    pi2 := Induce(Gal, 2);
    pi0 := Induce(Gal, 0);

    // Running through everything... eventually change so it's smarter.
    vprintf TameGenus, 1 : "Handling the potential Galois automorphisms.\n";
    tr := [];
    dims_t := [Dimension(U) : U in Frame(t)];
    p := Characteristic(K);
    for a in [1..Degree(E, K)-1] do
      S := Tensor(E, dims_t, [x^(p^a) : x in Eltseq(t)], TensorCategory(t));
      print "Building...";
      Forms_s := [((X @ pi2)^a)*F*Transpose((X @ pi2)^a) : F in SystemOfForms(s)];
      Forms_s := [&+[((X @ pi0)^(-a))[y][x]*Forms_s[y] : y in [1..#Forms_s]] : x in [1..#Forms_s]];
      print "tensors";
      s_p := Tensor(Forms_s, 2, 1, TensorCategory(t));
      print "TnOvCn";
      s_p := TensorOverCentroid(s_p);
      
      /*print "TESTING...";
      assert exists{k : k in E | k*s_p eq S}; // very slow 
      print "DONE.";*/

      check, M := TGIsPseudoIsometric(s_p, t);
      if check then
        Append(~tr, <a, M>);
      end if;
    end for;
    galois_gens := [__Galois_Tango(X, <pi2, pi0>, gamma[1], gamma[2], H) : gamma in tr];
    vprintf TameGenus, 1 : "Found %o Galois automorphisms.\n", #galois_gens;

    pseudo_in := [__RewriteMat(X, H.2) : X in pseudo_in];
    pseudo_out := [__RewriteMat(X, H.0) : X in pseudo_out];
    pseudo_order *:= Factorization(#galois_gens + 1);

    dims_s := [Dimension(X) : X in Frame(s)];
    pseudo_in cat:= [ExtractBlock(X, 1, 1, dims_s[1], dims_s[1]) : 
        X in galois_gens];
    pseudo_out cat:= [ExtractBlock(X, dims_s[1] + 1, dims_s[1] + 1, dims_s[3], 
        dims_s[3]) : X in galois_gens];

  end if;


  return pseudo_in, pseudo_out, isom_order*pseudo_order;
end function;

// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic TGPseudoIsometryGroup( t::TenSpcElt : Cent := true, Method := 0 ) -> 
    GrpMat
{Construct the pseudo-isometry group for an alternating bimap of genus 1 or 2. 
To use a specific method for genus 2, set Method to 1 for adjoint-tensor method 
or 2 for Pfaffian method.}
  require forall{ X : X in Frame(t) | Type(X) eq ModTupFld } : 
      "Domain and codomain must be vector spaces.";
  require Valence(t) eq 3 : "Tensor must have valence 3.";
  require IsAlternating(t) : "Tensor must be alternating.";
  K := BaseRing(t);
  require ISA(Type(K), FldFin) : "Base ring must be a finite field.";
  p := Characteristic(K);
  require p ne 2 : "Must be odd characteristic.";


  // Step 0: remove the radical.
  vprintf TameGenus, 1 : "Removing the radical... ";
  tt := Cputime();
  Rad := Radical(t, 2);
  Forms := SystemOfForms(t);

  if Dimension(Rad) gt 0 then
    C := Complement(Generic(Rad), Rad);
    RadPerm := GL(Dimension(Domain(t)[1]), K)!Matrix(Basis(C) cat Basis(Rad));
    nForms := [RadPerm*X*Transpose(RadPerm) : X in Forms];
    nForms := [ExtractBlock(X, 1, 1, Ncols(Forms[1])-Dimension(Rad), 
        Ncols(Forms[1])-Dimension(Rad)) : X in nForms];  
    t_nondeg := Tensor(nForms, 2, 1);
  else
    nForms := Forms;
    t_nondeg := t;
  end if; 

  timing := Cputime(tt);
  vprintf TameGenus, 1 : "%o seconds.\n", timing;


  // Step 1: write bimap over its centroid. 
  if Cent then
    vprintf TameGenus, 1 : "Rewriting tensor over its centroid... ";
    tt := Cputime();
    T, H := TensorOverCentroid(t_nondeg);
    require #BaseRing(T) eq #BaseRing(t) : "Extension fields not implemented.";
    vprintf TameGenus, 1 : "%o seconds.\n", Cputime(tt);
  else
    T := t_nondeg;
    dims_T := [Dimension(X) : X in Frame(T)];
    H := Homotopism(T, T, [*IdentityMatrix(K, dims_T[1]), 
        IdentityMatrix(K, dims_T[2]), IdentityMatrix(K, dims_T[3])*]);
  end if;

  // Check genus <= 2.
  require Dimension(Codomain(T)) le 2 : "Tensor is not genus 1 or 2.";


  // Step 2: Construct pseudo-isometry group
  if Dimension(Codomain(T)) eq 1 then

    // if genus 1, do a simpler algorithm.
    IN, OUT, ORD := __G1_PIsometry(T);
    // IS THIS ACTUALLY THE FULL GROUP???  --JM 

  else

    IN, OUT, ORD := __G2_PIsometry(T, H : Method := Method);

  end if;


  vprintf TameGenus, 1 : "Putting everything together... ";
  tt := Cputime();


  // Step 4: add pseudo-isometries on radical.
  if Dimension(Rad) gt 0 then
    Radgens := [DiagonalJoin(IdentityMatrix(K, Ncols(nForms[1])), x) : 
        x in Generators(GL(Dimension(Rad), K))];
    Radcentrals := [];
    for i in [1..Ncols(nForms[1])] do
      for j in [1..Dimension(Rad)] do
        X := IdentityMatrix(K, Ncols(nForms[1]) + Dimension(Rad));
        X[i][Ncols(nForms[1])+j] := 1;
        Append(~Radcentrals, X);
      end for;
    end for;
    pseudo_in := [DiagonalJoin(X, IdentityMatrix(K, Dimension(Rad))) : X in IN] 
        cat Radgens cat Radcentrals;
    pseudo_in := [RadPerm^-1 * pseudo_in[i] * RadPerm : i in [1..#pseudo_in]];
    pseudo_out := OUT cat [IdentityMatrix(K, #Forms) : 
        i in [1..#Radgens+#Radcentrals]];
    ORD *:= FactoredOrderGL(Dimension(Rad), #K);
    ORD *:= Factorization(#K)^(Dimension(C)*Dimension(Rad));
  else
    pseudo_in := IN;
    pseudo_out := OUT;
  end if;

  // Sanity check
  if __SANITY_CHECK then
    assert forall{i : i in [1..#pseudo_in] | IsHomotopism(t, t, [*pseudo_in[i],
        pseudo_in[i], pseudo_out[i]*], HomotopismCategory(3))};
  end if;

  // Put the group and relevant attributes together.
  PIsom := sub< GL(Ncols(Forms[1])+#Forms, K) | [DiagonalJoin(pseudo_in[i], 
      pseudo_out[i]) : i in [1..#pseudo_in]] >;
  DerivedFrom(~PIsom, t, {0..2}, {0, 2});
  PIsom`FactoredOrder := ORD;
  PIsom`Order := Integers()!ORD;

  timing := Cputime(tt);
  vprintf TameGenus, 1 : "%o seconds.\n", timing;

  return PIsom;
end intrinsic;
