__MatrixToAutomorphism := function( G, k, V, f, W, g, M )
  im := [];
  for i in [1..Dimension(V)] do
    vec := Eltseq( M[i] );
    image := ((V!vec[1..Dimension(V)]) @@ f) * ((W!vec[Dimension(V)+1..Dimension(V)+Dimension(W)]) @@ g);
    Append(~im, image);
  end for;
  return im;
end function;


/*
This is the function which combines both Pete's and Josh's code into one function for automorphisms.

Method: if set to 0, it uses the established cut offs for determining which method to use.
If set to 1, then we use the polynomial method, and if set to 2, we use the adjoint tensor method. 
*/

__SmallGenusAutomorphism := function( G, B : Method := 0, Print := false, Order := false )

  PIsom := PseudoIsometryGroupSG( B : Cent := false, Method := Method, Print := Print );
  k := BaseRing(B);
  V := B`Domain[1];
  f := B`Coerce[1];
  W := B`Codomain;
  g := B`Coerce[3];
  d := Dimension(V);
  genus := Dimension(W);

  if Print then
    printf "Putting everything together... ";
    tt := Cputime();
  end if;

  /* Step 6: Construct generators for Aut(G) */
  central := [];
  for i in [1..d] do
    for j in [1..genus] do
      M := IdentityMatrix( k, d+genus );
      M[i][d+j] := 1;
      Append(~central,M);
    end for;  
  end for;
  pseudo := [ PIsom.i : i in [1..Ngens(PIsom)] ];

  AutMat := sub< Generic( GL(d+genus,k) ) | pseudo, central >;
  AutMatGens := Generators( AutMat );
  dom := [ V.i @@ f : i in [1..Dimension(V)] ];// cat [ W.i @@ g : i in [1..Dimension(W)] ];
  AutGens := [ __MatrixToAutomorphism( G, k, V, f, W, g, X ) : X in AutMatGens ];
  
  //Sanity check
//  for im in AutGens do
//    beta := hom< G -> G | [<G.i,im[i]> : i in [1..Ngens(G)]] >;
//  end for;

  aut := AutomorphismGroup( G, dom, AutGens );
  aut`MatrixGroup := AutMat;

  if Print then
    timing := Cputime(tt);
    printf "%o seconds.\n", timing;
  end if;

  /* Optional */
  if Order then
    if Print then
      printf "Computing the order...";
    end if;
    tt := Cputime();
    aut`Order := LMGOrder( AutMat );
    timing := Cputime(tt);
    if Print then
      printf " %o seconds.\n", timing;
    end if;
  end if;

	return aut;
end function;


// Intrinsics ----------------------------------------------------------

intrinsic AutomorphismGroupSG( G::GrpPC : Cent := false, Method := 0, Print := false, Order := false ) -> GrpAuto
{Construct generators for the automorphism group of a small genus group G.
To use a specific method regardless of structure, set Method to 1 for adjoint tensor method or 2 for determinant method.}
  require IsPrime(Exponent(G)) : "Group must have exponent p.";
  require NilpotencyClass(G) le 2 : "Group is not class 2.";
  
  if IsAbelian(G) then
    return AutomorphismGroup(G);
  end if;

  B := pCentralTensor( G, 1, 1 );
  if Cent then
    if Print then
      printf "Rewriting bimap over its centroid... ";
      tt := Cputime();
    end if;
    B := TensorOverCentroid(B);
    if Print then
      printf "%o seconds.\n", Cputime(tt);
    end if;
    require IsPrimeField(BaseRing(B)) : "Currently only accepting prime fields.";
  end if;
  require Dimension(B`Codomain) le 2 : "Group is not genus 1 or 2.";

	return __SmallGenusAutomorphism( G, B : Method := Method, Print := Print, Order := Order );
end intrinsic;

