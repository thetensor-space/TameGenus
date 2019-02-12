/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "GlobalVars.m" : __VERSION, __SANITY_CHECK;


// -----------------------------------------------------------------------------
//                             Functions for printing
// -----------------------------------------------------------------------------

// A function to convert factored orders into a string parsable by humans.
__Display_order := function(N)
  if #N eq 0 then 
    return "1"; 
  end if;
  str := "";
  for t in N do
    str cat:= Sprintf("%o^%o * ", t[1], t[2]);
  end for;
  return str[1..#str-3];
end function;

__Print_field := procedure(t, str)
  if IsPrimeField(BaseRing(t)) then
    vprintf TameGenus, 1 : "\tCent(%o) = GF(%o)\n", str, #BaseRing(t);
  else
    vprintf TameGenus, 1 : "\tCent(%o) = GF(%o^%o)\n", str, 
        Factorization(#BaseRing(t))[1][1], Factorization(#BaseRing(t))[1][2];
  end if;
end procedure;

__Display_adj_info := procedure(A : subscript := "")
  assert RecognizeStarAlgebra(A);
  vprintf TameGenus, 1 : "\tdim(Adj%o) = %o\n", subscript, Dimension(A);

  if GetVerbose("TameGenus") eq 2 then

    Print_q := function(q)
      if IsPrime(q) then
        return IntegerToString(q);
      else
        t := Factorization(q)[1];
        return Sprintf("%o^%o", t[1], t[2]);
      end if;
    end function;

    simple := "";
    for S in SimpleParameters(A) do
      if S[1] eq "exchange" then
        simple cat:= Sprintf("Ex(%o, %o) x ", S[2], Print_q(S[3]));
      elif S[1] eq "symplectic" then
        simple cat:= Sprintf("Symp(%o, %o) x ", S[2], Print_q(S[3]));
      elif S[1] eq "unitary" then
        simple cat:= Sprintf("U(%o, %o) x ", S[2], Print_q(S[3]));
      elif S[1] eq "orthogonalplus" then
        simple cat:= Sprintf("O^+(%o, %o) x ", S[2], Print_q(S[3]));
      elif S[1] eq "orthogonalminus" then
        simple cat:= Sprintf("O^-(%o, %o) x ", S[2], Print_q(S[3]));
      else 
        simple cat:= Sprintf("O^o(%o, %o) x ", S[2], Print_q(S[3]));
      end if;
    end for;
  
    vprintf TameGenus, 2 : "\tSimple parameters = %o\n", simple[1..#simple-3];
  end if;
end procedure;

// -----------------------------------------------------------------------------
//                             Functions for tensors
// -----------------------------------------------------------------------------

__Radical_removal := function(t)
  K := BaseRing(t);

  vprintf TameGenus, 1 : "Checking the radicals.\n";
  tt := Cputime();

  Forms := SystemOfForms(t);
  Rad := Radical(t, 2);
  Crad := Coradical(t);

  vprintf TameGenus, 1 : "\tdim(Rad_V) = %o\n\tdim(Rad_W) = %o\n", 
      Dimension(Rad), Dimension(Crad);

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
    RadPerm := IdentityMatrix(K, Dimension(Domain(t)[1]));
  end if; 

  timing := Cputime(tt);
  vprintf TameGenus, 2 : "Radical timing : %o s\n", timing;

  return t_nondeg, Dimension(Rad), Dimension(Crad), RadPerm;
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
  Given a genus 2 tensor t, return the two subtensors t_flat and t_sloped, a 
  homotopism from t to t_flat perp t_sloped, and two sequences of the dimensions
  of the flat and sloped blocks.
*/
__Get_Flat_and_Sloped := function(t) 
  K := BaseRing(t);

	// Compute a perp-decomposition
	T, dims := PerpDecomposition(t);

  // Organize t into two subtensors
  flatdims := [ d : d in dims | IsOdd(d) ];
  slopeddims := [ d : d in dims | IsEven(d) ];
  Sort(~flatdims);
  Sort(~slopeddims);
  dims_sorted := flatdims cat slopeddims;
  P := __PermutationDegreeMatrix(K, dims, __FindPermutation(dims_sorted, dims)); 

  // To resolve some bugs about empty sequences:
  if flatdims eq [] then Append(~flatdims, 0); end if; 
  if slopeddims eq [] then Append(~slopeddims, 0); end if;
  
  // Construct the homotopism H from t to s:
  //    t : V x V >-> W
  //        ^   ^     |
  //        |   |     v
  //    s : V x V >-> W
  Antichmtp := TensorCategory([-1, -1, 1], {{0}, {1, 2}});
  H := Homotopism([*P*T, P*T, IdentityMatrix(K, 2)*], Antichmtp);
  s := t @ H;
  H := Homotopism(t, s, Maps(H), Antichmtp : Check := false);

  // Extract the two subtensors
  Flat := [ExtractBlock(X, 1, 1, &+flatdims, &+flatdims) : 
      X in SystemOfForms(s)];
  Sloped := [ExtractBlock(X, &+flatdims+ 1, &+flatdims + 1, &+slopeddims, 
      &+slopeddims) : X in SystemOfForms(s)];
  
  t_flat := Tensor(Flat, 2, 1, TensorCategory(t));
  t_sloped := Tensor(Sloped, 2, 1, TensorCategory(t));

  // Undo that change
  if flatdims eq [0] then flatdims := []; end if; 
  if slopeddims eq [0] then slopeddims := []; end if;

  return t_flat, t_sloped, H, flatdims, slopeddims;
end function;


/*
Input a matrix M
returns [  0   M ]
        [ -M^t 0 ].
*/
__Scharlau := function( M );
	k := Parent(M[1][1]);
  MA := MatrixAlgebra(k, Nrows(M) + Ncols(M));
  top := HorizontalJoin(ZeroMatrix(k, Nrows(M), Nrows(M)), M);
  bot := HorizontalJoin(-Transpose(M), ZeroMatrix(k, Ncols(M), Ncols(M)));
	return MA!VerticalJoin(top , bot);
end function;

// -----------------------------------------------------------------------------
//                           Functions for polynomials
// -----------------------------------------------------------------------------

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
  c := Coefficients(poly)[1]^(-1);
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

// -----------------------------------------------------------------------------
//                            Miscellaneous functions
// -----------------------------------------------------------------------------

// return true for adj-ten; false for Pfaffian
// m : method, q : size of field, d : dims
__WhichMethod := function(m, q, d)
  if m eq 1 then
    vprintf TameGenus, 1 : "\nMethod set to adjoint-tensor.\n";
    return true;
  end if;
  if m eq 2 then
    vprintf TameGenus, 1 : "\nMethod set to Pfaffian.\n";
    return false;
  end if;
  if q le 11 then
    vprintf TameGenus, 1 : "\nField is small enough, applying Pfaffian method.\n";
    return false;
  end if; 
  ord := Factorization(q);
  p := ord[1][1];
  e := ord[1][2];
  B := SequenceToMultiset(d);
  t := Maximum([Multiplicity(B, x) : x in B]);
  // can probably be improved
  if q^3*e le Factorial(t) then
    vprintf TameGenus, 1 : "\nPGammaL is smaller than potential symmetric " cat 
        "group, applying Pfaffian method.\n";
    return false;
  else
    vprintf TameGenus, 1 : "\nPGammaL is larger than symmetric group, " cat
        "applying adjoint-tensor method.\n";
    return true;
  end if;
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

Not really sure this is correct........
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

// Input: A pair of sequences of mats such that DiagonalJoin(X, Y) generates 
// PIsom/Isom.
// Returns a potentially smaller subsequence of X and Y, along with the order.
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


/*__WriteMatrixOverPrimeField := function( M )
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
end function;*/


// =============================================================================
//                                   Intrinsics
// =============================================================================

intrinsic TameGenusVersion() -> MonStgElt
{Returns the version number of TameGenus.}
  return __VERSION;
end intrinsic;
