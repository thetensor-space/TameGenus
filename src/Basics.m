import "Util.m" : __FindPermutation, __PermutationDegreeMatrix, __GL2ActionOnPolynomial;

intrinsic Genus( G::GrpPC ) -> RngIntElt
{Computes the genus of G.}
  require pClass(G) le 2 : "G is not p-class 2.";
  if IsAbelian(G) then
    return 0;
  end if;
  B := pCentralTensor(G,1,1);
  overC := TensorOverCentroid( B );
	return Dimension(overC`Codomain);
end intrinsic;

intrinsic Genus( T::TenSpcElt ) -> RngIntElt
{Computes the genus of T.}
  try 
    _ := Eltseq(T);
  catch err
    error "Cannot compute structure constants.";
  end try;
  overC := TensorOverCentroid( T );
	return Dimension(overC`Codomain);
end intrinsic;

__GetGenus2Signature := function( B )
  k := BaseRing(B);
  if not IsNondegenerate(B) then
    B := NondegenerateTensor(B);
  end if;
  A := AdjointAlgebra( B );
  T,dims := PerpDecomposition( SystemOfForms(B) : Adjoint := A );
  flats := Sort( [ d : d in dims | IsOdd(d) ] );
  sloped := Sort( [ d : d in dims | IsEven(d) ] );
  sorted_dims := flats cat sloped;
  P := __PermutationDegreeMatrix( k, dims, __FindPermutation( sorted_dims, dims ) );
  bForms := [ P*T*F*Transpose(P*T) : F in SystemOfForms(B) ];
  start := &+(flats cat [0]) + 1;
  R := PolynomialRing( k, 2 );
  polys := [];
  for d in sloped do
    X := ExtractBlock( bForms[1], start, start + d div 2, d div 2, d div 2);
    Y := ExtractBlock( bForms[2], start, start + d div 2, d div 2, d div 2);
    start +:= d;
    det := Determinant( X*R.1 + Y*R.2 );
    Append(~polys, Coefficients(det)[1]^-1 * det );
  end for;

  //Needed for PGL
  cleartop := function( X, k )
    if X[1][1] ne 0 then
      X := X[1][1]^-1 * MatrixAlgebra( k, 2 )!X;
    else
      X := X[1][2]^-1 * MatrixAlgebra( k, 2 )!X;
    end if;
    return X;
  end function;
  act := OrbitAction( GL(2,k), LineOrbits(GL(2,k))[1][1] ); // The action GL on the line (1,0)
  Perms := Image( act ); // PGL(2,k)

  // Get canonical Pfaffian.
  pfaff := &*polys;
  orbits := [ pfaff ];
  for Z in Perms do
    X := cleartop(Z @@ act, k);
    Include(~orbits, __GL2ActionOnPolynomial( pfaff, X ));
  end for;
  canonical_poly := Sort(orbits)[1]; // internal Magma ordering on K[x,y].
  factored_poly := Factorization(canonical_poly);
  can_polys := [ f[1] : f in factored_poly ]; 

  // Polynomials are annoying to compare... Here's the (possibly temporary) fix.
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

  return [* flats, terms *];
end function;

intrinsic Genus2Signature( Forms::[Mtrx] : Adjoint := 0, Cent := false ) -> List
{Returns the canonical genus 2 signature.
The first entry is the sequence of flat dimensions, and the second entry is the list of coefficients for the Pfaffians.}
  B := Tensor( Forms, 2, 1 );
  require IsAlternating(B) : "Forms must be alternating.";
  K := BaseRing(B);
  require Type(K) ne BoolElt : "Forms must be defined over the same field.";
  require ISA(Type(K),FldFin) : "Field must be finite.";
  B`Adjoint := Adjoint;
  if Cent then
    overC := TensorOverCentroid( B );
  else
    overC := B;
  end if;
  require Dimension(overC`Codomain) eq 2 : "Forms must be genus 2.";
  return __GetGenus2Signature( overC );
end intrinsic;

intrinsic Genus2Signature( G::GrpPC : Cent := false ) -> List
{Returns the canonical genus 2 signature.
The first entry is the sequence of flat dimensions, and the second entry is the list of coefficients for the Pfaffians.}
  require pClass(G) eq 2 : "G is not p-class 2.";
  B := pCentralTensor( G, 1, 1 );
  if Cent then
    overC := TensorOverCentroid( B );
  else
    overC := B;
  end if;
  require Dimension(overC`Codomain) eq 2 : "Not a genus 2 group.";
  return __GetGenus2Signature( overC );
end intrinsic;

intrinsic Genus2Signature( B::TenSpcElt : Cent := false ) -> List
{Returns the canonical genus 2 signature.
The first entry is the sequence of flat dimensions, and the second entry is the list of coefficients for the Pfaffians.}
  require forall{ X : X in B`Domain cat [*B`Codomain*] | Type(X) eq ModTupFld } : "Domain and codomain must be vector spaces.";
  require IsAlternating(B) : "Forms must be alternating.";
  K := BaseRing(B);
  require Type(K) ne BoolElt : "Forms must be defined over the same field.";
  require ISA(Type(K),FldFin) : "Field must be finite.";
  if Cent then
    B := TensorOverCentroid( B );
  end if;
  require Dimension(B`Codomain) eq 2 : "Not a genus 2 bimap.";
  return __GetGenus2Signature( B );
end intrinsic;
