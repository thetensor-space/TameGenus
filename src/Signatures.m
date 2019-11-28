/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "Util.m" : __GL2ActionOnPolynomial, __Get_Flat_and_Sloped, __MyIDMatrix, 
    __Radical_removal, __TensorOverCentroid;

__GetGenus2Signature := function(H)
  t := Codomain(H);
  K := BaseRing(t);
  A := AdjointAlgebra(t);

  // Just get the part we need: the sloped subtensor and the dims of the blocks.
  _, t_sloped, _, f_dims, s_dims := __Get_Flat_and_Sloped(t);

  if #s_dims gt 0 then

    R := PolynomialRing( K, 2 );
    Forms := SystemOfForms(t_sloped);
    polys := {@@};
    start := 1;
    for d in s_dims do
      X := ExtractBlock(Forms[1], start, start + d div 2, d div 2, d div 2);
      Y := ExtractBlock(Forms[2], start, start + d div 2, d div 2, d div 2);
      start +:= d;
      det := R!Determinant(X*R.1 + Y*R.2);
      Include(~polys, (Coefficients(det)[1])^-1 * det);
    end for;

    //Needed for PGL
    cleartop := function( X, K )
      if X[1][1] ne 0 then
        X := X[1][1]^-1 * MatrixAlgebra(K, 2)!X;
      else
        X := X[1][2]^-1 * MatrixAlgebra(K, 2)!X;
      end if;
      return X;
    end function;

    // The action GL on the line (1,0)
    act := OrbitAction(GL(2, K), LineOrbits(GL(2, K))[1][1]); 
    Perms := Image(act); // PGL(2, K)

    // Determine the potential Galois automorphisms
    k := BaseRing(Domain(H));
    if #K ne #k then
      powers := [Degree(k)*d : d in Divisors(Degree(K, k))];
    else
      powers := [0];
    end if;

    // Get canonical Pfaffian.
    pfaff_orbits := {@ polys @};
    for a in powers do
      for Z in Perms do // include Galois auts here
        X := cleartop(Z @@ act, K);
        polys_new := {@@};
        for f in polys do
          Include(~polys_new, __GL2ActionOnPolynomial(f, X : Gal := a));
        end for;
        Include(~pfaff_orbits, polys_new);
      end for;
    end for;
    pfaff_prod := {@ &*(P) : P in pfaff_orbits @};
    ind := Index(pfaff_prod, Minimum(pfaff_prod)); // internal Magma ordering 
    can_polys := [f : f in pfaff_orbits[ind]];

    // Polynomials are difficult to compare.
    // Here's the (possibly temporary) fix.
    terms := [* [ K!0 : i in [0..Degree(f)] ] : f in can_polys *];
    for i in [1..#can_polys] do
      f := can_polys[i];
      T := Terms(f); // sorted via lex
      C := Coefficients(f);
      d := Degree(f);
      assert #T eq #C;
      T := [ C[i]^-1*T[i] : i in [1..#T] ];
      for j in [1..#T] do
        terms[i][Degree(T[j],2)+1] +:= C[j];
      end for;
    end for;

  else
    terms := [**];
  end if;

  return [*f_dims, terms*];
end function;


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic Genus( t::TenSpcElt ) -> RngIntElt
{Computes the genus of the associated fully nondegenerate tensor of t.}
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  t_fn := __Radical_removal(t);
  T, _, success, issue := __TensorOverCentroid(t_fn, true);
  require success : issue;
  return Dimension(Codomain(T));
end intrinsic;

intrinsic Genus( G::GrpPC ) -> RngIntElt
{Computes the genus of p-group G.}
  require pClass(G) le 2 : "G is not p-class 2.";
  if IsAbelian(G) then
    return 0;
  end if;
	return Genus(pCentralTensor(G, 1, 1));
end intrinsic;

intrinsic Genus2Signature( t::TenSpcElt : Cent := true ) -> List
{Returns the canonical genus 2 signature. The first entry are the dimensions of 
the radical and co-radical, the second entry is the sequence of flat dimensions,
and the third entry is the list of coefficients for the Pfaffians.}
  require Type(Cent) eq BoolElt : "'Cent' must be true or false.";
  require forall{X : X in t`Domain cat [*t`Codomain*] | Type(X) eq ModTupFld} : 
      "Domain and codomain must be vector spaces.";
  require IsAlternating(t) : "Tensor must be alternating.";
  K := BaseRing(t);
  require ISA(Type(K), FldFin) : "Field must be finite.";

  t_fn := __Radical_removal(t);
  s, H, success, issue := __TensorOverCentroid(t_fn, Cent);
  require success : issue;
  require Dimension(Codomain(s)) le 2 : issue;
  
  return [*<Dimension(Radical(t, 2)), Dimension(Coradical(t))> *] cat
      __GetGenus2Signature(H);
end intrinsic;

intrinsic Genus2Signature( S::[Mtrx] : Cent := true ) -> List
{Returns the canonical genus 2 signature. The first entry are the dimensions of 
the radical and co-radical, the second entry is the sequence of flat dimensions,
and the third entry is the list of coefficients for the Pfaffians.}
  return Genus2Signature(Tensor(S, 2, 1) : Cent := Cent);
end intrinsic;

intrinsic Genus2Signature( G::GrpPC : Cent := true ) -> List
{Returns the canonical genus 2 signature. The first entry are the ranks of the 
center over the Frattini subgroup and the Frattini subgroup over the commutator
subgroup, the second entry is the sequence of flat dimensions, and the third 
entry is the list of coefficients for the Pfaffians.}
  return Genus2Signature(pCentralTensor(G, 1, 1) : Cent := Cent);
end intrinsic;

intrinsic IsTameGenusTensor( t::TenSpcElt ) -> BoolElt
{Decides if the given tensor is a tensor which can be handled by the TameGenus package.}
  s := __Radical_removal(t);
  if Dimension(Codomain(s)) le 2 or Dimension(Domain(s)[1]) eq 0 then
    return true;
  else 
    T, _, success, issue := __TensorOverCentroid(s, true);
    // This means that tensor is decomposable
    if not success then
      vprint TameGenus, 1 : issue;
      return false;
    end if;
    // This means that the tensor just has genus that is too large
    if Dimension(Codomain(T)) gt 2 then
      vprint TameGenus, 1 : "Group does not have genus 1 or 2.";
      return false;
    end if;
  end if;
  return true;
end intrinsic;

intrinsic IsTameGenusGroup( G::GrpPC ) -> BoolElt
{Decides if the given group is a group which can be handled by the TameGenus package.}
  prime_power, p, n := IsPrimePower(#G);
  // First we check that the group has the basic properties
  if (NilpotencyClass(G) gt 2) or (not prime_power) or 
    (p eq 2) or (Exponent(G) ne p) then
    vprint TameGenus, 1 : "Group is not an odd p-group of nilpotency class at most 2 with exponent p.";
    return false;
  end if;
  // Give abelian groups a pass
  if IsAbelian(G) then
    return true;
  end if;
  // Now we check the tensor has good properties
  t := pCentralTensor(G, p, 1, 1);
  return IsTameGenusTensor(t);
end intrinsic;
