/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/



/*
This is the function which combines both Pete's and Josh's code into one function for automorphisms.

Method: if set to 0, it uses the established cut offs for determining which method to use.
If set to 1, then we use the polynomial method, and if set to 2, we use the adjoint tensor method. 
*/

__TameGenusAutomorphism := function( G : Cent := true, Method := 0 )

  vprintf TameGenus, 1 : 
    "Extracting the p-central tensor and computing pseudo-isometries.\n";

  t := pCentralTensor(G);
  PIsom := TGPseudoIsometryGroup( t : Cent := Cent, Method := Method );

  vprintf TameGenus, 1 : 
    "Constructing automorphisms from pseudo-isometries:";
  tt := Cputime();

  k := BaseRing(t);
  V := t`Domain[1];
  f := t`Coerce[1];
  W := t`Codomain;
  g := t`Coerce[3];
  d := Dimension(V);
  e := Dimension(W);

  /* Step 6: Construct generators for Aut(G) */
  central := [];
  for i in [1..d] do
    for j in [1..e] do
      M := IdentityMatrix(k, d+e);
      M[i][d+j] := 1;
      Append(~central, M);
    end for;  
  end for;

  M_f := Matrix([G.i @ f : i in [1..d]]);
  M_g := Matrix([G.i @ g : i in [d+1..d+e]]);
  M := DiagonalJoin(M_f, M_g);
  pseudo := [M*X*M^-1 : X in Generators(PIsom)];
  AutMat := sub< GL(d+e, k) | pseudo, central >;

  if assigned PIsom`Order then
    AutMat`Order := PIsom`Order * (#k)^(d*e);
  end if;

  timing := Cputime(tt);
  vprintf TameGenus, 1 : "\t%o seconds.\n", timing;

	return AutMat;
end function;


// Intrinsics ----------------------------------------------------------

intrinsic TGAutomorphismGroup( G::GrpPC : Cent := true, Method := 0 ) -> GrpMat
{Returns the matrix group of automorphisms for the group G with tame genus.
To use a specific method, in the case of genus 2, regardless of structure set Method to 1 for adjoint-tensor method or 2 for Pfaffian method.}
  require IsPrime(Exponent(G)) : "Group must have exponent p.";
  require NilpotencyClass(G) le 2 : "Group is not class 2.";
  require Type(Cent) eq BoolElt : "`Cent' must be true or false.";
  require Type(Method) eq RngIntElt and Method in {0,1,2} : "`Method' must be an integer in {0, 1, 2}."; 
  
  if IsAbelian(G) then
    return AutomorphismGroup(G);
  end if;

	return __TameGenusAutomorphism( G : Cent := Cent, Method := Method );
end intrinsic;

