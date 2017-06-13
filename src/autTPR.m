/* 
    Copyright 2015--2017, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/

import "prelims.m": IsomorphismWithField;

// functions to compute the automorphism group of a truncated polynomial ring

/*
  Given <T> acting irreducibly on its underlying module, and positive
  integer <m>, return gens for the unit group of the Env(J(<T>,<m>)).
  Here J(<T>,<m>) denotes the (Murray-Jordan) block matrix with <T>
  on the diagonal, and the m x m identity above the diagonal.
*/


__unit_group := function (T, m)
     e := Nrows (T);
     d := e * m;
     k := BaseRing (Parent (T));
     EnvT, K, phi, psi := IsomorphismWithField (T);
     X := PrimitiveElement (K) @ psi;
     diag_gen := DiagonalJoin (< X : i in [1..m] >);
     uni_gens := [ ];
     one := Identity (MatrixAlgebra (k, d));
     for i in [1..m-1] do
	 for l in [0..Degree (k) * e - 1] do
	    ugen := one;
            for j in [1..m-i] do
	       InsertBlock (~ugen, X^l, e*(j-1)+1, e*i+e*(j-1)+1);
	    end for;
            Append (~uni_gens, ugen);
         end for;
     end for;
return [ diag_gen ] cat uni_gens;
end function;

/*
  Return unit group of Env(P(<T>,<part>)), where P(<T>,<part>) is
  an entire primary block.
*/
__unit_group_partition := function (T, part)
         assert forall { i : i in [1..#part-1] | part[i] le part[i+1] };
     m := part[#part];
     e := Nrows (T);
     Um := __unit_group (T, m);
     gens := [ ];
     for i in [1..#Um] do
         blocks := < >;
         for j in [1..#part] do
	    Append (~blocks, ExtractBlock (Um[i], 1, 1, e*part[j], e*part[j]));
	 end for;
         ui := DiagonalJoin (blocks);
         Append (~gens, ui);
     end for;
return gens;
end function;


// this can be done differently: see function below
__galois_generator_irred := function (J)
     MA := Generic (Parent (J));
     p := Characteristic (BaseRing (MA));
     M := RModule (sub < MA | J >);
     Mp := RModule (sub < MA | J^p >);
     isit, gamma := IsIsomorphic (M, Mp);
     assert isit;
     e := Degree (MinimalPolynomial (J));
     assert exists (l){ a : a in BaseRing (MA) | a ne 0 and Order (a*gamma) eq e };
return l * gamma;
end function;



/*
  given <X> conjugate to diag(J,...,J) with <J>
  irreducible return a generator for the Galois
  group of the field Env(<X>)
*/
__galois_generator_semisimple := function (X)
     mX := MinimalPolynomial (X);
     assert IsIrreducible (mX);
     e := Degree (mX);
     d := Nrows (X);
     assert d mod e eq 0;
     m := d div e;
     JX, C := JordanForm (X);
     J := ExtractBlock (JX, 1, 1, e, e);
     gammaJ := __galois_generator_irred (J);
     gamma := DiagonalJoin (< gammaJ : i in [1..m] >);
     gamma := GL (d, BaseRing (X))!gamma;
     assert Order (gamma) eq e;
return C^-1 * gamma * C;
end function;


/*
  In the case that the Jordan normal form of <X>
  is a single Jordan block, construct a generator
  for the Galois group of Env(<X>).
*/
__galois_generator_primary := function (X)

     mX := MinimalPolynomial (X);
     mXfac := Factorisation (mX);
     assert #mXfac eq 1;

     /* first see if it's semisimple ... i.e. Env(<X>) is a field */
     if mXfac[1][2] eq 1 then
         return __galois_generator_semisimple (X);
     end if;

     /* find a Wedderburn decomposition of Env(<X>) */
     J, W := WedderburnDecomposition (sub< Parent (X) | X >);

     /* look for a single generator of <W> */
     repeat
         Y := Random (W);
     until sub < W | Y > eq W;

     gamma := __galois_generator_semisimple (Y);

     assert forall{ i : i in [1..Ngens (W)] | 
                        gamma * W.i * gamma^-1 in W };

     assert forall{ i : i in [1..Ngens (J)] | 
                        gamma * J.i * gamma^-1 in J };

return gamma;
end function;



/*
  return generators for the group of "substitution"
  automorphisms of the ring Env(J(m,l)) where
  J(m,l) is the usual Jordan block of dimension m
  with eigenvalue l.

  Note that if J = J(m,l), then J is expressed
  relative to the basis 1,(J-l),...,(J-l)^(m-1). 
*/
  
__substitution_autogrp := function (m, l)

     /* set up the usual basis for the Jordan block */
     K := Parent (l);
     MA := MatrixAlgebra (K, m);
     I := Identity (MA);
     J := JordanBlock (MatrixAlgebra (K, 1)![l], m);
     MS := KMatrixSpace (K, m, m);
     MS := KMatrixSpaceWithBasis ([ MS!((J - l*I)^i) :
	   			        i in [0..m-1] ]);

     /* compute the units in Env(J) */
//     EJ := sub < Parent (J) | J, Identity (MA) >;
     gens := __unit_group (Matrix (1, 1, [l]), m);
     UEJ := sub < GL (m, K) | gens >;

     /* compute the effect of substitution on our basis */
     auto_gens := [ ];
     for u in Generators (UEJ) do
	 auto := [ Coordinates (MS, MS!((u*(J-l*I))^(i-1))) : i in [1..m] ];
         Append (~auto_gens, MA!Matrix (auto));
     end for;

     A := sub < GL (m, K) | auto_gens >;

return A;

end function;



/*
  Minimal polynomial of J is p(t)^m and is in (Murray) Jordan Form
*/

__AutGrpTPR_primary := function (J, part)
    
     k := BaseRing (J);
     n := Nrows (J);
     f := part[#part];
     e := n div (&+ part);
     d := e * f;

     Y := ExtractBlock (J, 1, 1, e, e);

              /* construct substitution generators */

     if (f eq 1) then   // J(Env(X)) = 0

         sub_gens := [ ];

     else

         /* first blow up the field and construct generators there */
         if Y eq 0 then 
            Y := Parent (Y)!1; 
         end if;
         EnvY, K, phi, psi := IsomorphismWithField (Y);
         sub_K := __substitution_autogrp (f, Y @ phi);

         /* next pull gens back into Aut(Env(X)) */
         sub_gens := [ ];
         for i in [1..Ngens (sub_K)] do

            z := sub_K.i;
            Z := MatrixAlgebra (k, d)!0;
            for s in [1..f] do
               for t in [1..f] do
	          InsertBlock (~Z, z[s][t] @ psi, (s-1)*e+1, (t-1)*e+1);
	       end for;
            end for;

            // embed pieces of Z diagonally
            ZZ := MatrixAlgebra (k, n)!0;
            pos := 1;
            for j in [1..#part] do
               nj := part[j] * e;
               bj := ExtractBlock (Z, 1, 1, nj, nj);
               InsertBlock (~ZZ, bj, pos, pos);
               pos +:= nj;
            end for;

            Append (~sub_gens, ZZ);

	 end for;
         
     end if;

             /* construct generator for Gal(EnvX/J(EnvX)) */
     q := #k;
     u := VectorSpace (k, e).1;
     gamma := Matrix ([ u * Y^(q*i) : i in [0..e-1] ]);
     blocks := < gamma : j in [1..n div e] >;
     gal_gen := GL (n, k)!DiagonalJoin (blocks);

            /* conjugate back */
     
     gens := sub_gens cat [ gal_gen ];

     A := sub < GL (n, k) | gens >;

         // check 
         assert  forall { i : i in [1..Ngens (A)] | A.i * J * A.i^-1 in
                                      sub < MatrixAlgebra (k, n) | J > };

return gal_gen, sub_gens;

end function;



