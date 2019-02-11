/* 
    Copyright 2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


__Galois_order := function(gens, n)
  Zn := CyclicGroup(GrpAb, n);
  H := sub< Zn | gens >;
  return FactoredOrder(H);
end function;

__RewriteMat := function(M, phi)
  V := Domain(phi);
  return Matrix([Eltseq(((V.i @ phi)*M) @@ phi) : i in [1..Dimension(V)]]);
end function;

__Galois_Tango := function(X, induce, k, M, H)
  top := __RewriteMat(M.2, H.2) * (X @ induce[1])^k;
  bot := __RewriteMat(M.0, H.0) * (X @ induce[2])^k;
  return DiagonalJoin(top, bot);
end function;

__galois_generator_irred := function (J)
     MA := Generic (Parent (J));
     q := #BaseRing (MA);
     M := RModule (sub < MA | J >);
     Mq := RModule (sub < MA | J^q >);
     isit, gamma := IsIsomorphic (M, Mq);
     assert isit;
     e := Degree (MinimalPolynomial (J));
     // Runs through the field, maybe fix at some point
     assert exists (l){ a : a in BaseRing (MA) | a ne 0 and Order (a*gamma) eq e }; 
return l * gamma;
end function;

// Input the centroid of the tensor.
// Most of this can be simplified.
__Galois_Cent := function(X)
  K := BaseRing(X);
  p := Characteristic(K);
  d := Nrows(X);
  e := Degree(MinimalPolynomial(X));

  // M is a C-module
  M := RModule(sub< Generic(Parent(X)) | X >);
  Inds := IndecomposableSummands(M);
  V := VectorSpace(K, d);
  U := sub< V | [V.i : i in [d - 2*e + 1..d]] >; 

  // Pete's trick to get the ind sums as actualy submodules.
  M_subs := [sub< V | [Vector(M!(Inds[i].j)) : j in [1..Ngens(Inds[i])]] > : 
      i in [1..#Inds]];
  indices_on_W := {@i : i in [1..#M_subs] | M_subs[i].1 ne U!0 and 
      M_subs[i].1 in U@};
  indices_on_V := {@k : k in [1..#M_subs]@} diff indices_on_W;

  // Get the order of M_subs to respect the block structure of C.
  M_subs_ord := [M_subs[i] : i in indices_on_V] cat 
      [M_subs[i] : i in indices_on_W];
  Inds_ord := [Inds[i] : i in indices_on_V] cat [Inds[i] : i in indices_on_W];
  Q := Matrix(&cat[Basis(S) : S in M_subs_ord]);
  N := M_subs_ord[1];

  // Action of X on the C-submodule N.
  X_N := Matrix([Coordinates(N, b*X) : b in Basis(N)]);
  
  // Use Pete's code to generate the conjugating element to get X_N^p. 
  Z := __galois_generator_irred(X_N);

  // Get conjugating elements from the isomorphism between the submodules.  
  conj := [*IdentityMatrix(K, e)*];
  for i in [2..#Inds] do
    isit, T := IsIsomorphic(Inds_ord[1], Inds_ord[i]);
    assert isit;
    Append(~conj, T);
  end for;

  // Put the blocks together
  blocks := <conj[i]^-1 * Z * conj[i] : i in [1..#Inds]>;
  T := DiagonalJoin(blocks);
  
  assert (Q^-1*T*Q)^-1*X*(Q^-1*T*Q) eq X^p;

  return Q^-1 * T * Q;
end function;


// returns the set of proper divisors of N (i.e. not including N).
__Proper_Divs := function(N)
  divs := Divisors(N);
  return Set(divs[1..#divs-1]);
end function;

// returns the subset S of D such that for all s in S, n does not divide s.
__Reduce_Divs := function(D, n)
  return {s : s in D | not IsDivisibleBy(s, n)};
end function;

__Standard_Gen := function(H)
  t := Codomain(H);
  E := BaseRing(t);
  X_s := ScalarMatrix(Dimension(Domain(t)[1]), E.1);
  Y_s := ScalarMatrix(Dimension(Codomain(t)), E.1);
  Z := DiagonalJoin(__RewriteMat(X_s, H.2), __RewriteMat(Y_s, H.0));
  assert DefiningPolynomial(E) eq MinimalPolynomial(Z);
  assert Z in Centroid(Domain(H));
  return Z;
end function;


__Galois_sanity := function(t, a)
  p := Characteristic(BaseRing(t));
  sigma := [*map< D -> D | x :-> Parent(x)![(u ne 0) select u^(-p^a) else 0 
      : u in Eltseq(x)] > : D in Domain(t)*];
  sigma cat:= [*map< Codomain(t) -> Codomain(t) | 
    x :-> Parent(x)![u^(p^a) : u in Eltseq(x)] >*];
  Antichmtp := TensorCategory([-1 : i in [1..#Domain(t)]] cat [1], 
      RepeatPartition(TensorCategory(t)));
  F := Homotopism(sigma, Antichmtp);
  return t @ F;
end function;


__Galois_check := function(H)
  s := Domain(H);
  t := Codomain(H);
  K := BaseRing(s);
  E := BaseRing(t);
  p := Characteristic(K);
  dims_s := [Dimension(U) : U in Frame(s)];
  dims_t := [Dimension(U) : U in Frame(t)];

  // Get generators of the centroid
  Y := __Standard_Gen(H);
  X := __Galois_Cent(Y);
  assert X^-1*Y*X eq Y^p;

  // TEST
  X2 := ExtractBlock(X, 1, 1, dims_s[1], dims_s[1]);
  X0 := ExtractBlock(X, dims_s[1] + 1, dims_s[1] + 1, dims_s[3], dims_s[3]);
  Cat := TensorCategory([-1, -1, 1], {{0}, {1, 2}});
  F_a := func< a | Homotopism([*X2^-a, X2^-a, X0^a*], Cat) >;

  gal_aut := [];
  divs := __Proper_Divs(Degree(E, K));

  while #divs gt 0 do
    // apply the Galois automorphism x :-> x^(p^a)
    a := Minimum(divs);

    // check if they are E-linear pseudo-isometric
    s_F := s @ F_a(a);
    assert Centroid(s) eq Centroid(s_F); // after tests *assign* this
    s_p := TensorOverCentroid(s_F);
    assert TGIsPseudoIsometric(s_p, __Galois_sanity(t, a)); 
    check, M := TGIsPseudoIsometric(t, s_p);

    // if so, remove multiplies of a; otherwise, just remove a. 
    if check then
      Append(~gal_aut, <a, M>);
      divs := __Reduce_Divs(divs, a);
    else
      Exclude(~divs, a);
    end if;

  end while;

  blocks := [<X2^(T[1]) * __RewriteMat(T[2].2, H.2), 
      X0^(T[1]) * __RewriteMat(T[2].0, H.0)> : T in gal_aut];

  assert forall{B : B in blocks | IsHomotopism(s, s, [*B[1], B[1], B[2]*], 
      HomotopismCategory(3))};

  Gal_ord := __Galois_order([T[1] : T in gal_aut], Degree(E, K));

  return blocks, Gal_ord;
end function;
