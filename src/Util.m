/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


import "GlobalVars.m" : __VERSION, __SANITY_CHECK;




__RewriteMat := function(M, phi)
  V := Domain(phi);
  return Matrix([Eltseq(((V.i @ phi)*M) @@ phi) : i in [1..Dimension(V)] ]);
end function;

__RewriteAuto := function(M, H, d, e)
  return DiagonalJoin(__RewriteMat(ExtractBlock(M, 1, 1, d, d), H.2), 
      __RewriteMat(ExtractBlock(M, d+1, d+1, e, e), H.0));
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
__Galois_Cent := function(C)
  K := BaseRing(C);
  p := Characteristic(K);
  d := Degree(C);
  e := Dimension(C);
  
  // Get the element that generates the unit group.
  isit, X := IsCyclic(C);
  assert isit;
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


// Input: DiagonalJoin(X, Y) generates PIsom/Isom.
__SmallerGenSet := function(X, Y)
  assert #X eq #Y;
  K := BaseRing(X[1]);
  Outer := sub< GL(2, K) | Y >;
  ORD := LMGFactoredOrder(Outer);
  Indices := {1..#Y};
  gens := [];
  while (#Indices gt 0) and 
      (ORD ne LMGFactoredOrder(sub< GL(2, K) | Y[gens] >)) do
    i := Random(Indices);
    Append(~gens, i);
    Exclude(~Indices, i);
  end while;
  return X[gens], Y[gens], ORD;
end function;


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
  PI := [__MatrixToAutomorphism(G, X) : X in Generators(M)];
  Cents := [];
  for i in [1..d] do
    for j in [1..e] do
      C := gen_set;
      C[i] *:= gen_set[d+j];
      Append(~Cents, C);
    end for;
  end for;

  A := AutomorphismGroup(G, gen_set, [gen_set @ alpha : alpha in PI] cat Cents);
  A`Order := #M * (#K)^(d*e);
  return A;
end function;

/*
Input a field k, a sequence of matrix degrees, and a permutation (#deg eq #perm)
returns a permutation matrix that acts on blocks of a prescribed size as the given permutation
*/
__PermutationDegreeMatrix := function(k, deg, perm)
	n:=#perm;
	P:=[];
	blocks:=[0 : i in [1..n]];
	for i in [1..n] do
		blocks[i]:=deg[Index(perm,i)];
	end for;
	for i in [1..n] do
		D:=0;
		for j in [1..perm[i]-1] do
			D+:=blocks[j];
		end for;
		for j in [1..deg[i]] do
			Append(~P,D+j);
		end for;
	end for;
	return Transpose(PermutationMatrix(k, P));
end function;

// Returns the permutation from S to T.
__FindPermutation := function( S, T );
    Stemp := S;
    Ttemp := T;
    n := #S;
    p1 := [ i : i in [1..n] ];
    p2 := p1;
    ParallelSort(~Stemp, ~p1);
    ParallelSort(~Ttemp, ~p2);
    p := [ p1[ Index( p2, i ) ] : i in [1..n] ];
    // Sanity
    //for i in [1..n] do
        //assert S[p] eq T;
    //end for;
return p;
end function;

/*
Input a polynomial f in k[x], and 
returns the homogenization of f in k[x,y].
*/
__Homogenization := function(f)
	K:=BaseRing(f);
	R:=PolynomialRing(K,2);
	n:=Degree(f);
	T:=Terms(f); // only nonzero terms
	C:=Coefficients(f); // includes zeros...
	poly:=0;
	j:=1;
	for i in [1..#C] do
		if C[i] ne 0 then
			m:=Degree(T[j]);
			poly+:=C[i]*R.1^m*R.2^(n-m);
			j+:=1;
		end if;
	end for;
	return poly;
end function;

/*
Input a polynomial f in k[x,y] and a 2x2 matrix Z and optional integer Gal for x :-> x^(p^Gal) auto.
returns monic f^Z.
*/
__GL2ActionOnPolynomial := function( f, Z : Gal := 0 )
	R := Parent(f);
  Z := Matrix(Z);
	phi := hom< R -> R | Z[1][1]*R.1+Z[1][2]*R.2, Z[2][1]*R.1+Z[2][2]*R.2 >;
  poly := f @ phi;
  c := Coefficients( poly )[1]^(-1);
  g := c * poly;
  if Gal eq 0 then
    return g;
  end if;
  p := Characteristic(BaseRing(R));
  h := R!0;
  for mon in Terms(g) do
    c := Coefficients(mon)[1];
    h +:= c^(p^Gal)*c^-1*mon;
  end for;
	return h;
end function;

/*
Input a matrix M
returns [  0   M ]
        [ -M^t 0 ].
*/
__Scharlau := function( M );
	k := Parent(M[1][1]);
	return MatrixAlgebra(k,Nrows(M)+Ncols(M))!VerticalJoin( HorizontalJoin( ZeroMatrix( k, Nrows(M), Nrows(M) ), M ), HorizontalJoin( -Transpose(M), ZeroMatrix( k, Ncols(M), Ncols(M) ) ) );
end function;

// Needed for __ExtractStarAlg
__IdentifyBasis := function (Q)
     U := Parent (Q[1]);
     flag := exists (i){ j : j in [1..#Q] | Q[j] ne U!0 };
     if not flag then
         return [];
     end if;
     positions := [i];
     remaining := [1..#Q];
     Remove (~remaining, i);
     extends := true;
     while extends do
         W := VectorSpaceWithBasis ([Q[c] : c in positions]);
         extends := exists (j){ i : i in [1..#remaining] | 
                                    not Q[remaining[i]] in W };
         if extends then
             Append (~positions, remaining[j]);
             Remove (~remaining, j);
         end if;
     end while;
return positions;
end function;

/*
Input a *-algebra A, a matrix T, and integers i,d
returns the *-algebra by conjugating by T and then extracting the dxd block starting at (i,i)
*/
__GetStarAlg := function( A, T, i, d )
  K := BaseRing(A);
  n := Degree(A);
  if d eq 0 or (d eq n and T eq Parent(T)!1) then
    AA := A;
  else
    S := T^-1;
    gens := [ < T*A.j*S, T*(A.j @ A`Star)*S > : j in [1..Ngens(A)] ];
    gens_block := [ < ExtractBlock(X[1],i,i,d,d), ExtractBlock(X[2],i,i,d,d) > : X in gens ];
    // remove blocks of 0's
    gens_block := {@ g : g in gens_block | g[1] ne Parent(g[1])!0 or g[2] ne Parent(g[2])!0 @};

    // Pete already built code for what we need.
    __Star_image := function (alg, MS, S, a)
      c := Coordinates (MS, MS!a);
      aa := &+[ c[i] * S[i] : i in [1..#c] ];
      return alg!aa;
    end function;
    StarOnBasis := function (A, S) 
      // first find a basis of the input <A>
      Q := [ Vector (A.i) : i in [1..Ngens (A)] ];
      positions := __IdentifyBasis (Q);
      bas := [ A.i : i in positions ];
      ims := [ S[i] : i in positions ];
      MS := KMatrixSpace (BaseRing (A), Degree (A), Degree (A));
      MS := KMatrixSpaceWithBasis ([ MS!(bas[i]) : i in [1..#bas] ]);
      return hom < A -> A | a :-> __Star_image (A, MS, ims, a) >;
    end function;

    AA := sub< MatrixAlgebra(K,d) | [ g[1] : g in gens_block ] >;
    star := StarOnBasis( AA, [ g[2] : g in gens_block ] );
    AA`Star := star;
    //assert RecognizeStarAlgebra(AA);
  end if;
  return AA;
end function;

// return true for adj-ten; false for Pfaffian
// m : method, q : size of field, d : dims
__WhichMethod := function(m,q,d)
  if m eq 1 then
    return true;
  end if;
  if m eq 2 then
    return false;
  end if;
  if q le 11 then
    return false;
  end if; 
  ord := Factorization(q);
  p := ord[1][1];
  e := ord[1][2];
  B := SequenceToMultiset( d );
  t := Maximum( [ Multiplicity( B, x ) : x in B ] );
  /* can be improved */
  if q^3*e le Factorial(t) then
    return false;
  else
    return true;
  end if;
end function;

__WriteMatrixOverPrimeField := function( M )
  E := BaseRing(M);
  p := Characteristic(E);
  K := GF(p);
  d := Degree(E,K);
  if d eq 1 then
    return M;
  end if;
  n := Nrows(M);
  V_ext := VectorSpace(E, n);
  V := VectorSpace(K, n*d);
  phi := map< V -> V_ext | x :-> V_ext!([ E!(Eltseq(x)[(j-1)*d+1..j*d]) : j in [1..n]]),
                           y :-> V!(&cat[Eltseq(y[i]) : i in [1..n]]) >;
  return Matrix(K, [ Eltseq(((V.i @ phi)*M) @@ phi) : i in [1..n*d] ]);
end function;

intrinsic TameGenusVersion() -> MonStgElt
{Returns the version number of TameGenus.}
  return __VERSION;
end intrinsic;
