import "Flat.m" : __StandardFIPair;
import "Util.m" : __Homogenization, __Scharlau;

__FormsToGroup := function( Forms : ExponentP := false )
  // We view the system of forms as structure constants for our desired group.
  n := Ncols( Forms[1] );
  m := #Forms;
  F := FreeGroup( n+m );
  k := Parent( Forms[1][1][1] );
  p := Characteristic( k );
  if ExponentP then
    Rels := [ F.i^p = 1 : i in [1..n+m] ];  
  else
    powers := RandomMatrix(GF(p),n,m);
    Rels := [ F.i^p = &*[ F.(n+j)^(Integers()!powers[i][j]) : j in [1..m] ] : i in [1..n] ] cat [ F.i^p = 1 : i in [n+1..n+m] ];
  end if;
  // Commutator relations from G/Z(G) x G/Z(G) --> G'
  for i in [1..n] do
    for j in [i+1..n] do
      RHS := F!1;
      for k in [1..m] do
        RHS *:= F.(n+k)^(Integers()!(Forms[k][j][i]));
      end for;
      // Sanity check
      // This verifies that the relation to be appended comes from the forms.
//      entries := [ Integers()!(Forms[l][j][i]) : l in [1..m] ];
//      compare := [ Multiplicity( SequenceToMultiset(Eltseq(RHS)), n+l ) : l in [1..m] ];
//      assert compare eq entries;
      // 
      Append(~Rels, (F.j, F.i) = RHS);
    end for;
  end for;
  // Commutator relations from G/Z(G) x Z(G) --> 1.
  for i in [1..n] do
    for j in [1..m] do
      Append(~Rels, (F.(n+j),F.i) = 1);
    end for;
  end for;
  Q := quo< F | Rels >;
  /* 
    Q is the group we want, but most computations in Magma do not want GrpFP.
    pQuotient is used to get a GrpPC which is isomorphic to Q.
    Note that structure constants of P will be pseudo-isometric to Forms,
    so in general the structure constants of P will not equal Forms.
  */
  if ExponentP then
    P := pQuotient( Q, p, 2 : Exponent := p );
  else
    P := pQuotient( Q, p, 2 );
  end if;
  return P;
end function;

__WriteOverPrimeField := function( Forms )
  M := Tensor(Forms,2,1);
  K := BaseRing(M);
  if IsPrimeField(K) then
    return Forms;
  end if;
  k := GF(Characteristic(K));
  e := Round(Log(#k, #K));
  D_old := M`Domain;
  D_new := [KSpace( k, Dimension(D)*e ) : D in D_old];
  C_old := M`Codomain;
  C_new := KSpace( k, Dimension(M`Codomain)*e );
  maps_D := [ map< D_new[i] -> D_old[i] | 
    x :-> D_old[i]![ K![ Coordinates(D_new[i],x)[j] : j in [(k-1)*e+1..k*e] ] : k in [1..Dimension(D_old[i])] ],
    y :-> D_new[i]!(&cat[ &cat[ Eltseq( s ) : s in Coordinates(D_old[i],y) ] ]) > : i in [1..#D_old] ];
  map_C := map< C_old -> C_new | 
    x :-> C_new!(&cat[ &cat[ Eltseq( s ) : s in Coordinates(C_old,x) ] ]),
    y :-> C_old![ K![ Coordinates(C_new,y)[j] : j in [(k-1)*e+1..k*e] ] : k in [1..Dimension(C_old)] ] >;
  F := function(x)
    return (< x[i] @ maps_D[i] : i in [1..#x] > @ M) @ map_C;
  end function;
  N := Tensor( D_new, C_new, F );
  //assert forall{ b : b in CartesianProduct( < [ c*K.1^i : i in [0..e-1], c in Basis(D) ] : D in D_old > ) | 
    //(b @ M) @ map_C eq < b[i] @@ maps_D[i] : i in [1..#b] > @ N };
  return SystemOfForms(N);
end function;

intrinsic RandomGroupSG( q::RngIntElt, n::RngIntElt, g::RngIntElt : Exponentp := false ) -> GrpPC
{Returns a random p-group with genus no larger than g of order q^(n+g), where q is a power of p.}
  require q ge 2 : "Argument 1 must be greater than 1.";
  require IsPrimePower(q) : "Argument 1 must be prime power.";
  require n gt 0 : "Argument 2 must be positive.";
  require g gt 0 : "Argument 3 must be positive.";

  Forms := __WriteOverPrimeField( [ M - Transpose(M) : M in [RandomMatrix(GF(q),n,n) : i in [1..g]] ] );
  return __FormsToGroup( Forms : ExponentP := Exponentp );
end intrinsic;

intrinsic RandomGenus2Group( q::RngIntElt, d::[RngIntElt] : Exponentp := false ) -> GrpPC
{Returns a random genus 2 p-group with prescribed block structure given by the sequence d, where q is a power of p.}
  require q ge 2 : "Argument 1 must be greater than 1.";
  require IsPrimePower(q) : "Argument 1 must be prime power.";
  K := GF(q);
  b1 := <>;
  b2 := <>;
  n := &+d;
  for dim in d do
    require dim ge 1 : "Dimensions must be positive.";
    if IsEven(dim) then
      if dim eq 2 then
        f := PolynomialRing(K).1 + Random(K);
      else
        f := RandomIrreduciblePolynomial( K, dim div 2 );
      end if;
      f := __Homogenization( f );
      I := IdentityMatrix( K, dim div 2 );
      R := Parent( f );
      phi := hom< R -> R | R.1, -1 >;
      _,g := IsUnivariate( f @ phi );
      C := CompanionMatrix( g );
      if Random( {0,1} ) eq 0 then
        Append(~b1, __Scharlau(I));
        Append(~b2, __Scharlau(C));
      else
        Append(~b1, __Scharlau(C));
        Append(~b2, __Scharlau(I));
      end if;
    else
      if dim eq 1 then
        Append(~b1,ZeroMatrix( K, 1, 1 ));
        Append(~b2,ZeroMatrix( K, 1, 1 ));
      else
        F,G := __StandardFIPair( K, (dim-1) div 2 );
        Append(~b1,F);
        Append(~b2,G);
      end if;
    end if;
  end for;
  B1 := DiagonalJoin( b1 );
  B2 := DiagonalJoin( b2 );
  T := Matrix(Random(GL(n,K)));
  B := __WriteOverPrimeField( [ T * B1 * Transpose(T), T * B2 * Transpose(T) ] );
  return __FormsToGroup( B : ExponentP := Exponentp );
end intrinsic;

intrinsic RandomGenus1Group( q::RngIntElt, d::RngIntElt, r::RngIntElt : Exponentp := false ) -> GrpPC
{Returns a random genus 1 p-group of order q^(d+r+1) where d is the rank of the form, r the dimension of the radical, and q a power of p.}
  require q ge 2 : "Argument 1 must be larger than 1.";
  require IsPrimePower(q) : "Argument 1 must be prime power.";
  require d ge 2 : "Argument 2 must be larger than 1.";
  require IsEven(d) : "Argument 2 must be even.";
  require r ge 0 : "Argument 3 must be nonnegative.";
  
  K := GF(q);
  n := d div 2;
  J := Matrix(K, [[0,1],[-1,0]] );
  F := DiagonalJoin( DiagonalJoin( < J : i in [1..n] > ), ZeroMatrix( K, r, r ) );
  X := Matrix(Random(GL(Ncols(F),K)));
  F := X*F*Transpose(X);
  B := __WriteOverPrimeField( [F] );
  return __FormsToGroup( B : ExponentP := Exponentp );
end intrinsic;
