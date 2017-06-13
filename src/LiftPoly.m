/* 
    Copyright 2015--2017, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/


import "Util.m": __GL2ActionOnPolynomial, __Scharlau, __WriteMatrixOverPrimeField;

/*
Input polynomials f,g in K[x,y] and Z in GL(2,K), and
returns an isotopism <X,Y,Z> such that 
		X (Ix+C_gy) Y = (Ix+C_fy)^Z.
*/

__LiftSlopeGenus2 := function( f,g,Z : Sanity := false, Gal := 0 )
	R:=Parent(f);
	K:=BaseRing(Z);
	G:=Parent(Z);
	n:=Degree(f);
	MA:=MatrixAlgebra(K,n);
	swap := [false,false];
	P := G![0,1,1,0];

	/* Check if f is divisible by y^n. Similar for g.
	If so, adjust Z accordingly	*/
	switch := hom< R -> R | R.2, R.1 >;
	if f/R.2^n in K then
		f := f@switch;
		swap[1] := true;
		Z := P*Z;
	end if;
	if g/R.2^n in K then
		g := g@switch;
		swap[2] := true;
		Z := Z*P;
	end if;

	a:=Z[1][1];
	b:=Z[1][2];
	c:=Z[2][1];
	d:=Z[2][2];
	
	pi:=hom< R -> R | R.1, -1 >;
	v,f_uni:=IsUnivariate(f@pi);
	v,g_uni:=IsUnivariate(g@pi);
	//assert (#Factorization( f_uni ) eq 1);
	//assert (#Factorization( g_uni ) eq 1);
	Cf:=MA!CompanionMatrix(f_uni);
	Cg:=MA!CompanionMatrix(g_uni);
	//assert Determinant( MA!1*R.1 + Cf*R.2 ) eq f; 
	//assert Determinant( MA!1*R.1 + Cg*R.2 ) eq g;

	/*
		Write Z = UPT. 
		Determine U, P, and T based on c.
	
		If c ne 0 then

    U = [ 1, a ]  P = [ 0, 1 ]  T = [ 1,   d/c    ] 
        [ 0, c ],     [ 1, 0 ],     [ 0, b - ad/c ].

    If c eq 0, then U and P are trivial and T = [ 1, b/a ]
                                                [ 0, d/a ].
	*/

	if c ne 0 then
		U:=G![ 1, a, 0, c ];
		T:=G![ 1, d*c^(-1), 0, b - a*d*c^(-1) ];
		v,fU_uni:=IsUnivariate( __GL2ActionOnPolynomial(f,U)@pi );
		v,gT_inv_uni:=IsUnivariate( __GL2ActionOnPolynomial(g,T^(-1))@pi ); 
		C1:=MA!CompanionMatrix(fU_uni);
		C2:=MA!CompanionMatrix(gT_inv_uni);
		RCF,M:=RationalForm( a*(MA!1)+c*Cf );
		RCF,N:=RationalForm( d*c^(-1)*(MA!1) + (b-a*d*c^(-1))*C2 );
		vec:=[n-k+1 : k in [1..n]];
		x:=PermutationMatrix(K,vec);

		//assert ExponentiateMatrix( [ MA!1, Cf ], U ) eq [ MA!1, M^(-1)*C1*M ];
		//assert ExponentiateMatrix( [ MA!1, C2 ], T ) eq [ MA!1, N^(-1)*Cg*N ];
		//assert x*C2*x*C1 eq MA!1;

		X:=M^(-1)*x*N^(-1);
		Y:=N*x*C1*M;
	else
		RCF,M:=RationalForm( b*a^(-1)*(MA!1)+d*a^(-1)*Cf );
		X:=a*M^(-1);
		Y:=M;
	end if;

	// If Z was changed above, undo that change.
	if swap[1] then
		Z := P*Z;
	end if;
	if swap[2] then
		Z := Z*P;
	end if;

	// sanity check
  if swap[1] then
      A := __Scharlau(Cf);
      B := __Scharlau(MA!1);
  else
      A := __Scharlau(MA!1);
      B := __Scharlau(Cf);
  end if;
  if swap[2] then
      C := __Scharlau(Cg);
      D := __Scharlau(MA!1); 
  else
      C := __Scharlau(MA!1);
      D := __Scharlau(Cg);
  end if;

  M := DiagonalJoin( X, Transpose(Y) );
  LHS := [ M * C * Transpose(M), M * D * Transpose(M) ];
  RHS := [ Z[1][i]*A + Z[2][i]*B : i in [1..2] ];
  //Verify <X,Y;Z> is a "pseudo-isometry."
  assert LHS eq RHS;

	return <X,Y,Z>;
end function;
