/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


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
    Rels := [ F.i^p = &*[ F.(n+j)^(Integers()!powers[i][j]) : j in [1..m] ] : 
        i in [1..n] ] cat [ F.i^p = 1 : i in [n+1..n+m] ];
  end if;
  // Commutator relations from G/Z(G) x G/Z(G) --> G'
  for i in [1..n] do
    for j in [i+1..n] do
      RHS := F!1;
      for k in [1..m] do
        RHS *:= F.(n+k)^(Integers()!(Forms[k][j][i]));
      end for;
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
  E := BaseRing(Forms[1]);
  if IsPrimeField(E) then
    return Forms;
  end if;
  K := GF(Characteristic(E));
  e := Degree(E, K);
  n := Ncols(Forms[1]);
  m := #Forms;
  V_E := VectorSpace(E, n);
  W_E := VectorSpace(E, m);
  V_K := VectorSpace(K, n*e);
  W_K := VectorSpace(E, m*e);

  V_map := map<V_K -> V_E | 
    x :-> V_E![E!(Eltseq(x)[e*(i-1)+1..e*i]) : i in [1..n]] >;
  W_map := map<W_E -> W_K | 
    x :-> W_K!(&cat[Eltseq(x[i]) : i in [1..m]]) >;
  
  new_Forms := [ZeroMatrix(K, n*e, n*e) : i in [1..m*e]];
  for i in [1..n*e-1] do
    u := Matrix(1, n, Eltseq(V_K.i @ V_map));
    for j in [i+1..n*e] do 
      v := Matrix(n, 1, Eltseq(V_K.j @ V_map));
      w := Eltseq((W_E![(u*X*v)[1][1] : X in Forms]) @ W_map);
      for k in [1..#w] do
        new_Forms[k][i][j] := w[k];
        new_Forms[k][j][i] := -w[k];
      end for;
    end for;
  end for;
  return new_Forms;
end function;

// Takes a homogeneous multivariate polynomial in 2 vars and returns a system of 
// forms.
__PolynomialToForms := function(f)
  R := Parent(f);
  K := BaseRing(R);
  n := 1;
  while f/(R.2^n) in R do
    n +:= 1;
  end while;
  g := f/(R.2^(n-1));
  if g eq R!1 then
    C := IdentityMatrix(K, 0);
    I := IdentityMatrix(K, 0);
  else
    h := Evaluate(g, [R.1, 1]);
    _, h := IsUnivariate(R!h);
    coeffs := Coefficients(h);
    C := CompanionMatrix((coeffs[#coeffs]^-1)*h);
    I := IdentityMatrix(K, Nrows(C));
  end if;
  if n gt 1 then
    C := DiagonalJoin(C, IdentityMatrix(K, n-1));
    _, r := IsUnivariate(R.2^(n-1));
    I := DiagonalJoin(I, CompanionMatrix(r));
  end if;
  Forms := __WriteOverPrimeField([ __Scharlau(I), __Scharlau(C) ]);
  return Forms;
end function;


// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// +++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

intrinsic TGRandomGroup( q::RngIntElt, n::RngIntElt, g::RngIntElt : 
    Exponentp := true ) -> GrpPC
{Returns a random p-group with genus no larger than g of order q^(n+g), where q 
is a power of p.}
  require q ge 2 : "Argument 1 must be greater than 1.";
  require IsPrimePower(q) : "Argument 1 must be prime power.";
  require n gt 1 : "Argument 2 must be larger than 1.";
  require g gt 0 : "Argument 3 must be positive.";
  require g le n*(n-1) div 2 : "Argument 3 must not exceed n(n-1)/2.";
  require Type(Exponentp) eq BoolElt : "Exponentp must be true or false.";
  if IsEven(q) then
    require not Exponentp :"Cannot construct nonabelian group with exponent 2.";
  end if;

  k := 0;
  repeat
    if k lt 100 then
      k +:= 1;
    else
      error "Could not construct a group with given parameters.";
    end if;
    AltForms := [M-Transpose(M) : M in [RandomMatrix(GF(q),n,n) : i in [1..g]]];
  until Dimension(sub< KMatrixSpace(GF(q), n, n) | AltForms>) eq g;
  
  Forms := __WriteOverPrimeField(AltForms);
  X := Random(GL(Nrows(Forms[1]), BaseRing(Forms[1])));
  Z := Random(GL(#Forms, BaseRing(Forms[1])));
  Forms := [X*F*Transpose(X) : F in Forms];
  Forms := [&+[Z[i][j]*Forms[i] : i in [1..#Forms]] : j in [1..#Forms]];
  grp := __FormsToGroup( Forms : ExponentP := Exponentp );
  return grp;
end intrinsic;

intrinsic RandomGenus2Group( q::RngIntElt, d::[RngIntElt] : Exponentp := true ) 
    -> GrpPC
{Returns a random genus 2 p-group with prescribed block structure given by the 
sequence d, where q is a power of p.}
  require q ge 2 : "Argument 1 must be greater than 1.";
  require IsPrimePower(q) : "Argument 1 must be prime power.";
  require Type(Exponentp) eq BoolElt : "Exponentp must be true or false.";

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
  B := __WriteOverPrimeField([ T * B1 * Transpose(T), T * B2 * Transpose(T) ]);
  return __FormsToGroup( B : ExponentP := Exponentp );
end intrinsic;

intrinsic RandomGenus1Group( q::RngIntElt, d::RngIntElt, r::RngIntElt : 
    Exponentp := true ) -> GrpPC
{Returns a random genus 1 p-group of order q^(2d+r+1) where 2d is the rank of 
the form, r the dimension of the radical, and q a power of p.}
  require q ge 2 : "Argument 1 must be larger than 1.";
  require IsPrimePower(q) : "Argument 1 must be prime power.";
  require d ge 1 : "Argument 2 must be positive.";
  require r ge 0 : "Argument 3 must be nonnegative.";
  require Type(Exponentp) eq BoolElt : "Exponentp must be true or false.";
  
  K := GF(q);
  J := Matrix(K, [[0,1],[-1,0]] );
  F := DiagonalJoin(DiagonalJoin(< J : i in [1..d] >), ZeroMatrix(K, r, r));
  X := Matrix(Random(GL(Ncols(F), K)));
  F := X * F * Transpose(X);
  B := __WriteOverPrimeField([F]);
  return __FormsToGroup(B : ExponentP := Exponentp);
end intrinsic;

intrinsic Genus2Group( P::[RngMPolElt] ) -> GrpPC
{Returns a central product of genus 2 groups where each group corresponds to a 
Pfaffian in the sequence.}
  require forall{f : f in P | IsHomogeneous(f)} : 
      "Polynomials must be homogeneous.";
  R := Parent(P[1]);
  require ISA(Type(BaseRing(R)),FldFin) : 
      "Coefficients must come from a finite field.";
  C := TensorCategory([1,1,1], {{0}, {1,2}});
  Blocks := [*__PolynomialToForms(f) : f in P*];
  Forms := [DiagonalJoin(<Blocks[i][j] : i in [1..#Blocks]>) : 
      j in [1..#Blocks[1]]];
  t := Tensor(Forms, 2, 1, C);  
  return HeisenbergGroupPC(t);
end intrinsic;

intrinsic Genus2Group( P::[RngUPolElt] ) -> GrpPC
{Returns a central product of genus 2 groups where each group corresponds to a 
Pfaffian in the sequence.}
  R := Parent(__Homogenization(P[1]));
  return Genus2Group([R!__Homogenization(f) : f in P]);
end intrinsic;

intrinsic Genus2Group( f::RngMPolElt ) -> GrpPC
{Returns a genus 2 group whose Pfaffian is equivalent to the homogeneous 
polynomial f.}
  return Genus2Group([f]);
end intrinsic;

intrinsic Genus2Group( f::RngUPolElt ) -> GrpPC
{Returns a genus 2 group whose Pfaffian is equivalent to f.}
  return Genus2Group([f]);
end intrinsic;
