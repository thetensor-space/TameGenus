/*
Input a field k, a sequence of matrix degrees, and a permutation (#deg eq #perm)
returns a permutation matrix that acts on blocks of a prescribed size as the given permutation
*/
__PermutationDegreeMatrix := function(k,deg,perm)
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
	return Transpose( PermutationMatrix(k, P) );
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
