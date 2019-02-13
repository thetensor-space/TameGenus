/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "Util.m" : __GL2ActionOnPolynomial, __Get_Flat_and_Sloped;

__GetGenus2Signature := function( t )
  K := BaseRing(t);
  A := AdjointAlgebra(t);

  // Just get the part we need: the sloped subtensor and the dims of the blocks.
  _, t_sloped, _, _, dims := __Get_Flat_and_Sloped(t);

  if #dims gt 0 then

    R := PolynomialRing( k, 2 );
    Forms := SystemOfForms(t_sloped);
    polys := {@@};
    start := 1;
    for d in dims do
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

    // Get canonical Pfaffian.
    pfaff_orbits := {@ polys @};
    for Z in Perms do // include Galois auts here
      X := cleartop(Z @@ act, K);
      polys_new := {@@};
      for f in polys do
        Include(~polys_new, __GL2ActionOnPolynomial(f, X));
      end for;
      Include(~pfaff_orbits, polys_new);
    end for;
    pfaff_prod := {@ &*(P) : P in pfaff_orbits @};
    ind := Index(pfaff_prod, Minimum(pfaff_prod)); // internal Magma ordering 
    can_polys := [f : f in pfaff_orbits[ind]];

    // Polynomials are difficult to compare.
    // Here's the (possibly temporary) fix.
    terms := [* [ 0 : i in [0..Degree(f)] ] : f in can_polys *];
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

  return [* flats, terms *];
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
  s := TensorOverCentroid(FullyNondegenerateTensor(t));
	return Dimension(Codomain(s));
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

  t_nondeg := FullyNondegenerateTensor(t);
  if Cent then
    s, H := TensorOverCentroid(t_nondeg);
  end if;
  
  require Dimension(Codomain(s)) eq 2 : "Not a genus 2 tensor.";

  return [*<Dimension(Radical(t, 2)), Dimension(Coradical(t))> *] cat
      __GetGenus2Signature(s);
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
