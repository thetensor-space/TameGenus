/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "GlobalVars.m" : __SANITY_CHECK;

// Code due to E. A. O'Brien from 31.01.2019.
// vector to integer sequence
__VectorToInt := function (v)
  r := Eltseq(v);
  ChangeUniverse(~r, Integers());
  return r;
end function;


// Code due to E. A. O'Brien from 31.01.2019.
/* convert matrix A in GL(d, p) describing action on Frattini quotient
    of d-generator p-group G into automorphism of G */
__MatrixToAutomorphism := function (P, A)
  p := FactoredOrder(P)[1][1];
  d := FrattiniQuotientRank(P);
  m := Nrows(A);
  error if m lt d, "Must define action on at least Frattini quotient";
  zeros := [0: i in [1..NPCgens(P) - m]];
  Images := [<P.i, P!(__VectorToInt(A[i]) cat zeros)> : i in [1..m]];

  if __SANITY_CHECK then 
    return hom <P -> P | Images >;
  else
    return hom <P -> P | Images : Check := false >;
  end if;
end function;


/*
  Given a matrix group of pseudo-isometries of G and a tensor constructed via 
  pCentralTensor(G), construct the corresponding automorphisms of G.
*/
__PseudoIsom_to_GrpAuto := function(M, t)
  assert assigned t`Coerce;
  G := Domain(t`Coerce[1]);
  d := Dimension(Domain(t)[1]);
  e := Dimension(Codomain(t));
  K := BaseRing(t);
  
  gen_set := Isetseq(PCGenerators(G));
  assert #gen_set eq d + e;
  if __SANITY_CHECK then
    vprintf TameGenus, 1 : "\nRunning sanity check.\n";
    tt := Cputime();
  end if;
  PI := [__MatrixToAutomorphism(G, X) : X in M];
  if __SANITY_CHECK then
    vprintf TameGenus, 2 : "Sanity test timing : %o s\n", Cputime(tt);
  end if;
  Cents := [];
  for i in [1..d] do
    for j in [1..e] do
      C := gen_set;
      C[i] *:= gen_set[d+j];
      Append(~Cents, C);
    end for;
  end for;

  A := AutomorphismGroup(G, gen_set, [gen_set @ alpha : alpha in PI] cat Cents);

  return A;
end function;


/*
  This is the function which combines both Pete's and Josh's code into one 
  function for automorphisms.

  Method: if set to 0, it uses the established cut offs for determining which 
  method to use. If set to 1, then we use the polynomial method, and if set to 
  2, we use the adjoint tensor method. 
*/

__TameGenusAutomorphism := function( G : Cent := true, Method := 0, 
    Mat := false )

  vprintf TameGenus, 1 : 
    "Extracting the p-central tensor and computing pseudo-isometries.\n";

  // Tensor
  t := pCentralTensor(G, 1, 1);
  _ := Eltseq(t);
  t`Reflexive`Alternating := true;
  t`Reflexive`Antisymmetric := true;
  
  // Pseudo-isometry group
  PIsom := TGPseudoIsometryGroup(t : Cent := Cent, Method := Method);


  vprintf TameGenus, 1 : 
    "\nConstructing automorphism group from pseudo-isometries.\n";
  tt := Cputime();

  // Adjust by the coercsion maps
  K := BaseRing(t);
  V := t`Domain[1];
  f := t`Coerce[1];
  W := t`Codomain;
  g := t`Coerce[3];
  d := Dimension(V);
  e := Dimension(W);

  M_f := Matrix([G.i @ f : i in [1..d]]);
  M_g := Matrix([G.i @ g : i in [d+1..d+e]]);
  M := DiagonalJoin(M_f, M_g^-1);
  pseudo := [M^-1*X*M : X in Generators(PIsom)];

  if Mat then
    // Step 6: Construct generators for Aut(G) 
    central := [];
    for i in [1..d] do
      for j in [1..e] do
        M := IdentityMatrix(K, d+e);
        M[i][d+j] := 1;
        Append(~central, M);
      end for;  
    end for;

    A := sub< GL(d+e, K) | pseudo, central >;
  else
    A := __PseudoIsom_to_GrpAuto(pseudo, t);
  end if;

  // Record orders
  ORD := FactoredOrder(PIsom) * Factorization(#K)^(d*e);
  if Mat then 
    A`FactoredOrder := ORD;
  end if;
  A`Order := Integers()!ORD;

  vprintf TameGenus, 2 : "Automorphism group construction : %o s\n", 
      Cputime(tt);

	return A;
end function;


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic TGAutomorphismGroup( G::GrpPC : Cent := true, Method := 0, 
    Mat := false ) -> GrpAuto
{Returns the group of automorphisms of the group G with tame genus. To use a 
specific method, in the case of genus 2, regardless of structure set Method to 1 
for adjoint-tensor method or 2 for Pfaffian method.}
  require IsPrime(Exponent(G)) : "Group must have exponent p.";
  require NilpotencyClass(G) le 2 : "Group is not class 2.";
  require Type(Cent) eq BoolElt : "'Cent' must be true or false.";
  require Type(Method) eq RngIntElt and Method in {0,1,2} : 
      "'Method' must be an integer in {0, 1, 2}."; 
  require Type(Mat) eq BoolElt : "'Mat' must be true or false.";
  
  // Just call Magma funcion for the abelian case.
  if IsAbelian(G) then
    return AutomorphismGroup(G);
  end if;

  P, phi := pQuotient(G, Exponent(G), 2 : Print := 0);
  A := __TameGenusAutomorphism(P : Cent := Cent, Method := Method, Mat := Mat);

  if Mat then
    Aut_G := A;
  else
    G_gens := [x : x in Generators(G)];
    Aut_G := AutomorphismGroup(G, G_gens, [G_gens @ phi @ alpha @@ phi : 
        alpha in Generators(A)]);
    Aut_G`Order := A`Order;
    Aut_G`Group := G;
  end if;

  return Aut_G;
end intrinsic;

