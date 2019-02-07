/* 
    Copyright 2015--2019, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under MIT License.
*/


import "forms.m" : MyOrthogonalComplement;
import "prelims.m" : JordanNormalForm, 
                    __tensor_over_adj, 
                    IsomorphismBetweenFields, 
                   __permutation_matrix, 
                    IsConjugateCyclic;
import "autTPR.m" : __AutGrpTPR_primary;
import "ronyai.m" : __is_translate;

/*
   File created May, 2012, based on conversation with James in Dec, 2011.
   The goal is to set up the computational infrastructure for an effective
   test of pseudo-isometry between two bimaps of corank 2.
*/


// Exhaustive method: will usually work fine.
__is_sloped_A := function (F, G)
     if Rank (G) eq Nrows (G) then
         return true, G, F;
     end if;
     k := BaseRing (Parent (F));
     flag := exists (a){ b : b in k | 
                             Nrows (F + b*G) eq Rank (F + b*G) };
     if flag then
         X := F + a*G;
         Y := G;
         return true, X, Y;
     else
         return false, _, _;
     end if;
end function;

// Polytime version based on discussions with James in Jan 2015.
__is_sloped_B := function (F, G)
     if Rank (G) eq Nrows (G) then
         return true, G, F;
     end if;
     k := BaseRing (Parent (G));
     R<y> := PolynomialRing (k);
     MA := MatrixAlgebra (R, Nrows (G));
     pol := Determinant (MA!F + y * MA!G);
     if pol eq 0 then
         return false, _, _;
     end if;
     roots := [ r[1] : r in Roots (pol) ];
     isit := exists (a){ b : b in k | not b in roots };
     if isit then
         X := F + a*G;
         Y := G;
         return true, X, Y;
     else
         return false, _, _;
     end if;
end function;

/*
   Given a pair of alternating forms, determine whether or not
   the associated genus 2 bimap is sloped and, if so, return 
   a slope and the form pair used to construct it.
*/
IsSloped := function (F, G)
     if (Rank (F) + Rank (G) ge Nrows (F)) or (#BaseRing (F) lt 5^3) then
         return __is_sloped_A (F, G);
     else
         return __is_sloped_B (F, G);
     end if;
end function;



/*
   <Y> a proper subspace of <X>
   choose x in <X> minus <Y>
*/
__not_in := function (X, Y)
    found := false;
    count := 0;
    while not found and count lt 100 do
       count +:= 1;
       x := Random (X);
       if not x in Y then found := true; end if;
    end while;
    if found then return x; else return 0; end if;
end function;


/* 
    Given alternating forms <F> (nondegenerate) and <G> such that
    J = G*F^-1 has minimal polynomial a power of a single irreducible,
    find bases for common, opposite t.i. subspaces relative to <F> and <G>.
    
    The function follows Goldstein & Guralnick.
*/

__TIDecompPrimary := function (F, G)

     d := Nrows (F);
     k := BaseRing (Parent (F));
     V := VectorSpace (k, d);
     J := G * F^-1;
     mfac := Factorisation (MinimalPolynomial (J));
     assert #mfac eq 1;
     p := mfac[1][1];
     f := mfac[1][2];

     /* find two complementary t.i. subspaces */
     JJ := Evaluate (p^(f-1), J);
     null := Nullspace (JJ);
     u := __not_in (V, null);
     uperp := MyOrthogonalComplement (V, sub<V|u * JJ>, F);
     w := __not_in (V, uperp);
     w := w / InnerProduct (u*JJ*F, w);

     U := sub < V | [ u * J^i : i in [0..Degree(p)*f - 1] ] >;
     W := sub < V | [ w * J^i : i in [0..Degree(p)*f - 1] ] >;
     assert Dimension (U) eq Dimension (W);
     assert Dimension (U meet W) eq 0;
     assert forall { i : i in [1..Ngens (U)] |
              forall { j : j in [1..Ngens (U)] |
                 InnerProduct (U.i * F, U.j) eq 0 } };
     assert forall { i : i in [1..Ngens (W)] |
              forall { j : j in [1..Ngens (W)] |
                 InnerProduct (W.i * F, W.j) eq 0 } };
                 
     UB := [ U.i : i in [1..Ngens (U)] ];
     WB := [ W.i : i in [1..Ngens (W)] ];
     L := sub < V | UB cat WB >;
     
     /* if L is not the whole space, recurse to orthogonal complement */
     if L ne V then  
         Lperp := MyOrthogonalComplement (V, L, F);
         e := Dimension (Lperp);
         FF := MatrixAlgebra (k, e)![ 
                 [ InnerProduct (Lperp.i * F, Lperp.j) : i in [1..e] ] :
                        j in [1..e] ];
         GG := MatrixAlgebra (k, e)![ 
                 [ InnerProduct (Lperp.i * G, Lperp.j) : i in [1..e] ] :
                        j in [1..e] ];
         ULperpB, WLperpB := $$ (FF, GG);   // recursive call
         ULperpB := [ &+ [ ULperpB[i][j] * Lperp.j : j in [1..e] ] : 
                           i in [1..#ULperpB] ];
         WLperpB := [ &+ [ WLperpB[i][j] * Lperp.j : j in [1..e] ] : 
                           i in [1..#WLperpB] ];
         UB cat:= ULperpB;
         WB cat:= WLperpB;
     end if;
  
return UB, WB;   

end function;


/* 
    Given any alternating forms <F> (nondegenerate) and <G>, find
    bases for common, opposite t.i. subspaces relative to <F> and <G>.
*/

__TIDecomp := function (F, G)

     d := Nrows (F);
     k := BaseRing (Parent (F));

     assert Rank (F) eq d;

     J := G * F^-1;
     mfac := Factorisation (MinimalPolynomial (J));
     t := #mfac;

     /* proceed sequentially through the primary components */
     UB := [ ];
     WB := [ ];
     for i in [1..t] do
	       
	       pi := mfac[i][1];
           ei := mfac[i][2];
           fi := pi^ei;   
           Ji := Evaluate (fi, J);
           Vi := Nullspace (Ji);
           di := Dimension (Vi);
           
           Fi := MatrixAlgebra (k, di)![ 
                 [ InnerProduct (Vi.s * F, Vi.t) : s in [1..di] ] :
                        t in [1..di] ];
           Gi := MatrixAlgebra (k, di)![ 
                 [ InnerProduct (Vi.s * G, Vi.t) : s in [1..di] ] :
                        t in [1..di] ];
           UiB, WiB := __TIDecompPrimary (Fi, Gi);
           UiB := [ &+ [ UiB[s][t] * Vi.t : t in [1..di] ] : 
                           s in [1..#UiB] ];
           WiB := [ &+ [ WiB[s][t] * Vi.t : t in [1..di] ] : 
                           s in [1..#WiB] ];
           UB cat:= UiB;
           WB cat:= WiB;
           
     end for;
     
return UB, WB;    

end function;


/* 
    Again assume <F> is nondegenerate. Internal function to transform
    the pair <F>, <G> to a pair of the form:
    
        <X> = [   0   I_m ]    <Y> = [   0    J  ]
              [ -I_m   0  ]          [ -J^t   0  ]
              
    where <J> is in Jordan Normal Form. Also returns the conjugating
    matrix, and the information needed to recover the Jordan form.
*/

TransformSlopedPair := function (F, G)

     k := BaseRing (Parent (F));
     d := Nrows (F);
     assert d mod 2 eq 0;
     m := d div 2;

     UB, WB := __TIDecomp (F, G);
     C := Matrix (UB cat WB);
     X := C * F * Transpose (C);
     Y := C * G * Transpose (C);

     /* we have:

        <X> = [   0   X0  ]    <Y> = [   0   Y0  ]
              [ -X0^t  0  ]          [ -Y0^t  0  ]
      
      with X0 invertible.     
      */
      
      X0 := ExtractBlock (X, 1, m+1, m, m);
      S, U, V := SmithForm (X0);
      assert Rank (S) eq m;
      C2 := MatrixAlgebra (k, d)!0;
      InsertBlock (~C2, U, 1, 1);
      InsertBlock (~C2, Transpose (V), m+1, m+1);
      X := C2 * X * Transpose (C2);
      Y := C2 * Y * Transpose (C2);
      C := C2 * C;
      
      /* now we have:

        <X> = [   0   I_m ]    <Y> = [   0   Y0  ]
              [ -I_m   0  ]          [ -Y0^t  0  ]
         
      */
      
      /* convert Y0 to Jordan form and collect representation info */
      Y0 := ExtractBlock (Y, 1, m+1, m, m);
      J0, C0, info := JordanNormalForm (Y0);
      C3 := DiagonalJoin (C0, Transpose (C0^-1));
      X := C3 * X * Transpose (C3);
      Y := C3 * Y * Transpose (C3);
      C := C3 * C;
      
return X, Y, C, info;   

end function;


/*
  Constructive test of whether <g> is pseudo-isometry from 
  <S1> to <S2>; if true,find associated outer map.
*/

IsPseudoIsometry := function (g, S1, S2)
     e := #S1;
     k := BaseRing (Parent (g));
     d := Degree (Parent (g));
     MS := KMatrixSpace (k, d, d);
     U1 := KMatrixSpaceWithBasis ([ MS!(g * S1[i] * Transpose (g)) : i in [1..e] ]);
     U2 := KMatrixSpaceWithBasis ([ MS!(S2[i]) : i in [1..e] ]);
     if U1 ne U2 then 
         return false, _;
     end if;
     mat := Matrix ([ Coordinates (U2, U1.i) : i in [1..e] ]);
return true, GL (e, k)!mat;
end function;


/*
  This is just an internal test for pseudo-isometries of the tensor bimap
*/

__IsPseudoIsometry := function (g, W, pi : Vgen := [ ], gbar := false)

     e := Dimension (W);
     k := BaseRing (Parent (g));
     d := Degree (Parent (g));
     V := VectorSpace (k, d);

     /* find vectors in <V> that give a basis for <W> */
     if #Vgen eq 0 then
         count := 0;
         found := false;
         while (not found) and (count lt 5) do
	     count +:= 1;
             Vgen := [ < Random (V) , Random (V) > : i in [1..e] ];
             Wbas := [ TensorProduct (Vgen[i][1], Vgen[i][2]) @ pi : i in [1..e] ];
             if Dimension (sub < W | Wbas >) eq e then
                  found := true;
             end if;
         end while;
         assert found;
     else
         assert #Vgen eq e;
         Wbas := [ TensorProduct (Vgen[i][1], Vgen[i][2]) @ pi : i in [1..e] ];
     end if;

     if Type (gbar) eq BoolElt then
         /* find the matrix induced by <g> on <W> */
         g_mat := Matrix (
                   [ TensorProduct (Vgen[i][1] * g, Vgen[i][2] * g) @ pi : i in [1..e] ]
                                  );
         if Rank (g_mat) lt e then
            return false, _;
         end if;
         gbar := GL (e, k)!g_mat; 
     end if;

     /* check if ( <g> , <gbar> ) is really a pseudo-isometry */
     for i in [1..d] do
         for j in [1..d] do
	           wij := TensorProduct (V.i, V.j) @ pi;
               wijg := TensorProduct (V.i * g, V.j * g) @ pi;
               isit := (wijg eq wij * gbar);
               if not isit then
                  return false, _;
               end if;
	 end for;
     end for;

return isit, gbar;

end function;

/*
   Special case when F, G span a 1-dimensional form space.
*/
__PseudoIsometryGroupGenus1 := function (F, G)

      k := BaseRing (Parent (F));
      
      // ensure that F has full rank
      if F eq 0 then
          FF := G;
          GG := F;
          t := GL (2, k)![0,1,1,0];
      else
          FF := F;
          GG := G;
          t := Identity (GL (2, k));
      end if;
      assert Rank (FF) eq Nrows (FF);
      
      // ensure that G = 0
      S := GG * FF^-1;
      assert IsScalar (S);
      s := S[1][1];
      t *:= GL (2, k)![1,0,-s,1];
      assert (GG - s * FF eq 0);
      
      // construct similarities of F and build corresponding outer maps
      H := SimilarityGroup (FF);
      Hgens := [ H.i : i in [1..Ngens (H)] ];
      HH0gens := [ ];
      for i in [1..#Hgens] do
          h := Hgens[i];
          S := h * FF * Transpose (h) * FF^-1;
          assert IsScalar (S);
          s := S[1][1];
          hh := GL (2, k)![ s , 0 , 0 , 1 ];
          Append (~HH0gens, hh);
      end for;
      
      // add in the other generators
      Hgens cat:= [ Identity (Generic (H)) : i in [1,2] ];
      Append (~HH0gens, GL (2, k)![1,0,0,PrimitiveElement(k)]);
      Append (~HH0gens, GL (2, k)![1,1,0,1]);
      
      // conjugate back to original basis
      HHgens := [ t^-1 * HH0gens[i] * t : i in [1..#HH0gens] ];
      
      // sanity check
      sane := true;
      for i in [1..#Hgens] do
          h := Hgens[i];
          hh := HHgens[i];
          sane and:= (h * F * Transpose (h) eq (hh[1][1] * F + hh[1][2] * G));
          sane and:= (h * G * Transpose (h) eq (hh[2][1] * F + hh[2][2] * G));
      end for;
      assert sane;
      
return Hgens, HHgens;

end function;


/*
  Input: a sloped, alternating bimap of genus 2, specified
         by a basis of alternating forms.
         Changed to take a tensor instead. JM (5/26/16)
  Output: generators for the quotient of pseudo-isometry group
         of the bimap by its isometry group.
*/

PseudoIsometryGroupAdjointTensor := function (B)

     F := SystemOfForms(B)[1];
     G := SystemOfForms(B)[2];

     d := Degree (Parent (F));
     d2 := d div 2;
     k := BaseRing (Parent (F));
     MA := MatrixAlgebra (k, d);
     ma := MatrixAlgebra (k, d2);
     
     
     /* check to see if F, G span a 1-dimensional space */
     MS := KMatrixSpace (k, d, d);
     if Dimension (sub < MS | [ MS!F , MS!G] >) lt 2 then
          return __PseudoIsometryGroupGenus1 (F, G);
     end if;
     
     /* check sloped */
     isit, FF, GG := IsSloped (F, G);
     assert isit;


     /* change basis so that the common slope has the form diag(<x>,<x>) */ 
     X, Y, C, info := TransformSlopedPair (FF, GG);
     dbl := Y * X^-1;

     /* compute the adjoint algebra and its center */
     A := AdjointAlgebra ([X, Y]);
     R := sub < MA | Identity (MA), dbl >;

     flag, Rtimes := UnitGroup (R);
     assert flag;

         // sanity check 
         assert Centre (A) eq R;

     /* form the tensor product over A relative to new basis */
     A_pairs := [ < A.i , A.i @ A`Star > : i in [1..Ngens (A)] ];
     flag, VtenV, pi, pair := __tensor_over_adj (A_pairs, dbl);
     if not flag then
         return false;
     end if;
     m := Dimension (VtenV);

         // sanity check
         assert m eq Degree (MinimalPolynomial (dbl));

         // check that this output behaves as it should
         u := pair[1];
         v := pair[2];
         assert forall { i : i in [1..m] | 
                         TensorProduct (u, v * dbl^(i-1)) @ pi eq VtenV.i };

     /* obtain pseudo-isometries of the tensor bimap arising from autos of Env(<dbl>) */
     x := ExtractBlock (dbl, 1, 1,  d2, d2);
     one := Identity (MatrixAlgebra (k, d));
     gal_gens := [ ];
     sub_gens := [ ];
     pos := 1;
     centres := < >;
     degrees := [ ];

     for i in [1..#info] do   // number of primary components

	     mi := Degree (info[i][1]) * (&+ info[i][2]);
         Append (~degrees, mi);
         xi := ExtractBlock (x, pos, pos, mi, mi);
         Ji := ExtractBlock (xi, 1, 1, Degree (info[i][1]), Degree (info[i][1]));
         Append (~centres, Ji);         

         gal_gen_i, sub_gens_i := __AutGrpTPR_primary (xi, info[i][2]);

         // modify Galois generator
         if (gal_gen_i ne gal_gen_i^0) then
            gal_i := one;
            InsertBlock (~gal_i, gal_gen_i, pos, pos);
            InsertBlock (~gal_i, Transpose (gal_gen_i^-1), d2 + pos, d2 + pos);
            Append (~gal_gens, gal_i);
         end if;

         // modify substitution generators
         for j in [1..#sub_gens_i] do
            sub_ij := one;
            InsertBlock (~sub_ij, sub_gens_i[j], pos, pos);
            InsertBlock (~sub_ij, Transpose (sub_gens_i[j]^-1), d2 + pos, d2 + pos);
            Append (~sub_gens, sub_ij);
	     end for;            
         
         pos +:= mi;

     end for;

     aut_gens := gal_gens cat sub_gens; 

     /* construct permutation automorphisms */
     rep_info := [ ];
     for i in [1..#info] do
        f := info[i][1];
        Append (~rep_info, < Degree (f), info[i][2] >);
    end for;
    
    orbits := [ [ i : i in [1..#rep_info] | rep_info[i] eq x ] : 
                       x in Set (rep_info) ];

    perm_gens := [ ];
    sym := SymmetricGroup (#info);

    for O in orbits do

       if #O gt 1 then

  	      symO := SymmetricGroup (#O);

          for pi in Generators (symO) do

   	         blocks := < Identity (MatrixAlgebra (k, degrees[i])) : 
   	                                             i in [1..#degrees] >;
 
             /* coerce <symO> into <sym> */
             L := [1..#degrees];
             for i in [1..#O] do
                j := i^pi;
                L[O[i]] := O[j];
             end for;
             PI := sym!L;

	         /* modify relevant blocks */
             for i in O do
                j := i^PI;
                if (i ne j) then
		           b := IsomorphismBetweenFields (centres[j], centres[i]);
                   B := DiagonalJoin (
                            < b : s in [1..(degrees[i] div (Nrows (centres[i])))] >
					                  );
                   blocks[i] := B;
  	            end if;
	         end for;

             pi_gen := __permutation_matrix (blocks, PI);
             Append (~perm_gens, pi_gen);

	      end for;

        end if;

     end for;

     /* sanity check */
     assert forall { y : y in perm_gens | 
                         y * x * y^-1 in sub < ma | Identity (ma), x > };

     // modify permutation generators
     pgens := [ ];
     for j in [1..#perm_gens] do
        pgen := one;
        InsertBlock (~pgen, perm_gens[j], 1, 1);
        InsertBlock (~pgen, Transpose (perm_gens[j]^-1), d2 + 1, d2 + 1);
        Append (~pgens, pgen);
     end for;

     aut_gens cat:= pgens;

     /* verify that they are pseudo-isometries and get the associated outer maps */
     Vgen := [ < u , v * dbl^(i-1) > : i in [1..m] ];
     aut_gens_tensor := [ ];
     
     for s in [1..#aut_gens] do
         a := aut_gens[s];
         isit, abar := __IsPseudoIsometry (a, VtenV, pi : Vgen := Vgen);
         assert isit;
         Append (~aut_gens_tensor, abar);
     end for;
     aut := sub < GL (d, k) | aut_gens >;
     aut_tensor := sub < GL (m, k) | aut_gens_tensor >;
     RandomSchreier (aut);
     RandomSchreier (aut_tensor);
     bar := hom < aut -> aut_tensor | aut_gens_tensor >;

         /* factor b through W and compute its kernel */
         H := KMatrixSpace (k, m, 2)!0;
         for i in [1..m] do
	     H[i][1] := InnerProduct (Vgen[i][1] * X, Vgen[i][2]);
             H[i][2] := InnerProduct (Vgen[i][1] * Y, Vgen[i][2]);
         end for;
         K := Nullspace (H);

     /* use Ronyai to find subgroup of <R>* stabilising <K> */
     S, f := Algebra (R);  // convert to structure constant model
     ZR := [ &+ [ (K.i)[j] * dbl^(j-1) : j in [1..m] ] : i in [1..Ngens (K)] ];
     Z := [ ZR[i] @ f : i in [1..#ZR] ];
     isit, good := __is_translate (S, Z, Z);
     assert isit;   // at least the identity of <S> does the trick
     stab_R_K := sub < R | [ good[i] @@ f : i in [1..#good] ] >;
     flag, stab_Rtimes_K := UnitGroup (stab_R_K);

     /* modify to give pseudo-isometries */
     PSEUDO_gens := [ InsertBlock (stab_Rtimes_K.i, Identity (ma), 1, 1) :
			     i in [1..Ngens (stab_Rtimes_K)] ];
     PSEUDO_gens_tensor := [ ];
     for i in [1..#PSEUDO_gens] do
	     mu_r := PSEUDO_gens[i];
         isit, rbar := __IsPseudoIsometry (mu_r, VtenV, pi : Vgen := Vgen);
         assert isit;
         Append (~PSEUDO_gens_tensor, rbar);
     end for;

     /* now loop through the automorphisms of <R> */
     autos_bar := [ abar : abar in aut_tensor ]; 

     for abar in autos_bar do

          a := abar @@ bar;           
          Ka := K * abar;
          ZRa := [ &+ [ (Ka.i)[j] * dbl^(j-1) : j in [1..m] ] : 
                                     i in [1..Ngens (Ka)] ];
          Za := [ ZRa[i] @ f : i in [1..#ZRa] ];
          isit, good := __is_translate (S, Za, Z);

          if isit then   // find a unit that translates
          
              // exhaustive search for invertible transporter
              // if this becomes expensive, will need to reformulate
              // the random approach.         
              found := exists (u){ v : v in VectorSpace (k, #good) |
                  Rank((&+ [ v[i] * good[i] : i in [1..#good] ]) @@ f) eq d };

              // random approach (possibly) not reliable enough as coded
              /*
              LIMIT := 10;
              found := false;
              count := 0;
              while (count lt LIMIT) and (not found) do
                  count +:= 1;
                  c := [ Random (k) : i in [1..#good] ];
                  s := &+ [ c[i] * good[i] : i in [1..#good] ];
                  r := s @@ f;
                  if Rank (r) eq d then
                     found := true;
                  end if;
             end while;
             */

             if not found then
                 "...no unit found!!";
             else
                 r := (&+ [ u[i] * good[i] : i in [1..#good] ]) @@ f;
                 mu_r := InsertBlock (r, Identity (ma), 1, 1);
                 isit, rbar := __IsPseudoIsometry (mu_r, VtenV, pi : Vgen := Vgen);
                 assert isit;
                 Append (~PSEUDO_gens, a * mu_r);
                 Append (~PSEUDO_gens_tensor, abar * rbar);
                 assert K * abar * rbar eq K;
                 assert IsPseudoIsometry (a * mu_r, [X,Y], [X,Y]);
             end if;

         end if;
         
     end for;

     /*conjugate back again */
     inner_gens := [ C^-1 * PSEUDO_gens[i] * C : i in [1..#PSEUDO_gens] ];
     
          // final sanity check, and build the outer pseudo-isometries
          outer_gens := [ ];
          for i in [1..#inner_gens] do
              isit, hh := IsPseudoIsometry (inner_gens[i], [F,G], [F,G]);  
              assert isit;
              Append (~outer_gens, hh);
          end for;   

return inner_gens, outer_gens;

end function;



/*
  Input: two sloped, alternating bimaps of genus 2, specified
         by bases of alternating forms.
  Output: true if the bimaps are pseudo-isometric (together with
         inner and outer pseudo-isometries); false otherwise.
*/

IsPseudoIsometricAdjointTensor := function (B, C)
     pair1 := SystemOfForms(B);
     pair2 := SystemOfForms(C);
     F1 := pair1[1];  G1 := pair1[2];
     F2 := pair2[1];  G2 := pair2[2];

     d := Degree (Parent (F1));
     d2 := d div 2;
     k := BaseRing (Parent (F1));
     MA := MatrixAlgebra (k, d);
     ma := MatrixAlgebra (k, d2);
     
/* edit by PAB on 4/7/2016 after bug report from J. Maglione */
/* check that <F1,G1> and <F2,G2> are both 2-dimensional */
/*if (Dimension (sub < KMatrixSpace (k,d,d) | F1 , G1 >) ne 2 or
   Dimension (sub < KMatrixSpace (k,d,d) | F2 , G2 >) ne 2) then
   return false, _, _;
end if; */
// above check moved to the main Iso code whenever adj-tens gets called. -Josh

     /* check that <b1> is sloped */
     isit, F1, G1 := IsSloped (F1, G1);
     assert isit;

     /* check that <b1> is sloped */
     isit, F2, G2 := IsSloped (F2, G2);
     assert isit; 

     /* transform <b1> to standard form */ 
     X1, Y1, C1, info := TransformSlopedPair (F1, G1);
     dbl1 := Y1 * X1^-1; 

     /* transform <b2> to standard form */
     XX2, YY2, C2, info := TransformSlopedPair (F2, G2);
     dbl2 := YY2 * XX2^-1;
     
     /* conjugate the adjoint algebras */
     sgl1 := ExtractBlock (dbl1, 1, 1, d2, d2);
     sgl2 := ExtractBlock (dbl2, 1, 1, d2, d2);
     S1 := sub < MatrixAlgebra (k, d2) | sgl1, Identity (ma) >;
     isit, M := IsConjugateCyclic (sgl2, S1);

     if not isit then
         "adjoint algebras are not conjugate";
         return false, _, _;
     end if;

     /* compute the adjoint algebra of <b1> and its center */
     A1 := AdjointAlgebra ([X1, Y1]);
     R := sub < MA | dbl1, Identity (MA) >;
     flag, Rtimes := UnitGroup (R);
     assert flag;
 
         assert Centre (A1) eq R;

     C_adj := DiagonalJoin (M, Transpose (M^-1));
     X2 := C_adj * XX2 * Transpose (C_adj);
     Y2 := C_adj * YY2 * Transpose (C_adj);
     A2 := AdjointAlgebra ([X2, Y2]);
 
     // temporary sanity check that involutions align 
     assert forall { i : i in [1..Ngens (A1)] | 
             (A1.i) @ A1`Star eq (A1.i) @ A2`Star };

     /* form the tensor product over A relative to new basis */
     adj_pairs := [ < A1.i , A1.i @ A1`Star > : i in [1..Ngens (A1)] ];
     flag, VtenV, pi, pair := __tensor_over_adj (adj_pairs, dbl1);
     if not flag then
         return false, _, _;
     end if;
     m := Dimension (VtenV);

         // SANITY CHECK: the dimension of <VtenV> is correct
         assert m eq Degree (MinimalPolynomial (dbl1));

         // SANITY CHECK: that this output behaves as it should
         u := pair[1];
         v := pair[2];
         assert forall { i : i in [1..m] | 
                         TensorProduct (u, v * dbl1^(i-1)) @ pi eq VtenV.i };


     /* obtain pseudo-isometries of the tensor bimap arising from autos of Env(<dbl>) */
     one := Identity (MatrixAlgebra (k, d));
     gal_gens := [ ];
     sub_gens := [ ];
     pos := 1;
     centres := < >;
     degrees := [ ];

     for i in [1..#info] do   // number of primary components

	     mi := Degree (info[i][1]) * (&+ info[i][2]);
         Append (~degrees, mi);
         xi := ExtractBlock (sgl1, pos, pos, mi, mi);
         Ji := ExtractBlock (xi, 1, 1, Degree (info[i][1]), Degree (info[i][1]));
         Append (~centres, Ji);         

         gal_gen_i, sub_gens_i := __AutGrpTPR_primary (xi, info[i][2]);

         // modify Galois generator
         if (gal_gen_i ne gal_gen_i^0) then
            gal_i := one;
            InsertBlock (~gal_i, gal_gen_i, pos, pos);
            InsertBlock (~gal_i, Transpose (gal_gen_i^-1), d2 + pos, d2 + pos);
            Append (~gal_gens, gal_i);
         end if;

         // modify substitution generators
         for j in [1..#sub_gens_i] do
            sub_ij := one;
            InsertBlock (~sub_ij, sub_gens_i[j], pos, pos);
            InsertBlock (~sub_ij, Transpose (sub_gens_i[j]^-1), d2 + pos, d2 + pos);
            Append (~sub_gens, sub_ij);
	     end for;
            
         pos +:= mi;

     end for;
     aut_gens := gal_gens cat sub_gens; 

     /* construct permutation automorphisms */
     rep_info := [ ];
     for i in [1..#info] do
        f := info[i][1];
        c := Coefficients (f);
        if c[1] eq 0 then
            assert #c eq 2;
            Append (~rep_info, <0,info[i][2]>);
        else
            Append (~rep_info, <Degree (f), info[i][2]>);
        end if;
    end for;
    
    orbits := [ [ i : i in [1..#rep_info] | rep_info[i] eq x ] : 
                       x in Set (rep_info) ];

    perm_gens := [ ];
    sym := SymmetricGroup (#info);

    for O in orbits do

       if #O gt 1 then

  	      symO := SymmetricGroup (#O);

          for pi in Generators (symO) do

   	         blocks := < Identity (MatrixAlgebra (k, degrees[i])) : 
   	                                             i in [1..#degrees] >;
 
             /* coerce <symO> into <sym> */
             L := [1..#degrees];
             for i in [1..#O] do
                j := i^pi;
                L[O[i]] := O[j];
             end for;
             PI := sym!L;

	         /* modify relevant blocks */
             for i in O do
                j := i^PI;
                if (i ne j) then
		           b := IsomorphismBetweenFields (centres[j], centres[i]);
                   B := DiagonalJoin (
                            < b : s in [1..(degrees[i] div (Nrows (centres[i])))] >
					                  );
                   blocks[i] := B;
  	            end if;
	         end for;

             pi_gen := __permutation_matrix (blocks, PI);
             Append (~perm_gens, pi_gen);

	      end for;

        end if;

     end for;

     /* SANITY CHECK: permutation matrices induce ring automorphisms */
     assert forall { y : y in perm_gens | 
           y * sgl1 * y^-1 in sub < ma | sgl1 , Identity (ma) > };

     // modify permutation generators
     pgens := [ ];
     for j in [1..#perm_gens] do
        pgen := one;
        InsertBlock (~pgen, perm_gens[j], 1, 1);
        InsertBlock (~pgen, Transpose (perm_gens[j]^-1), d2 + 1, d2 + 1);
        Append (~pgens, pgen);
     end for;

     aut_gens cat:= pgens;

     /* verify that they are pseudo-isometries and get the associated outer maps */
     Vgen := [ < u , v * dbl1^(i-1) > : i in [1..m] ];
     aut_gens_tensor := [ ];
     for s in [1..#aut_gens] do
         a := aut_gens[s];
         isit, abar := __IsPseudoIsometry (a, VtenV, pi : Vgen := Vgen);
         assert isit;
         Append (~aut_gens_tensor, abar);
     end for;
     aut := sub < GL (d, k) | aut_gens >;
     aut_tensor := sub < GL (m, k) | aut_gens_tensor >;
     RandomSchreier (aut);
     RandomSchreier (aut_tensor);
     bar := hom < aut -> aut_tensor | aut_gens_tensor >;


         /* factor the bimaps through W and compute their kernels */
         H1 := KMatrixSpace (k, m, 2)!0;
         H2 := KMatrixSpace (k, m, 2)!0;
         for i in [1..m] do
	         H1[i][1] := InnerProduct (Vgen[i][1] * X1, Vgen[i][2]);
             H1[i][2] := InnerProduct (Vgen[i][1] * Y1, Vgen[i][2]);
             H2[i][1] := InnerProduct (Vgen[i][1] * X2, Vgen[i][2]);
             H2[i][2] := InnerProduct (Vgen[i][1] * Y2, Vgen[i][2]);
         end for;
         K1 := Nullspace (H1);
         K2 := Nullspace (H2);

     /* now loop through the automorphisms of <R> */
     autos_bar := [ abar : abar in aut_tensor ];

     S, f := Algebra (R);  // convert to structure constant model
     Z1R := [ &+ [ (K1.i)[j] * dbl1^(j-1) : j in [1..m] ] : i in [1..Ngens (K1)] ];
     Z1 := [ Z1R[i] @ f : i in [1..#Z1R] ];  

      found := false;
      i := 0;
      while (not found) and (i lt #autos_bar) do

          i +:= 1;
          abar := autos_bar[i];
          a := abar @@ bar;           
          K2a := K2 * abar;
          Z2Ra := [ &+ [ (K2a.i)[j] * dbl1^(j-1) : j in [1..m] ] : 
                                     i in [1..Ngens (K2a)] ];
          Z2a := [ Z2Ra[i] @ f : i in [1..#Z2Ra] ];
          isit, good := __is_translate (S, Z2a, Z1);

          if isit then   // find a unit that translates

          // exhaustive search for invertible transporter
          // if this becomes expensive, will need to reformulate
          // the random approach.         
          found := exists (u){ v : v in VectorSpace (k, #good) |
              Rank((&+ [ v[i] * good[i] : i in [1..#good] ]) @@ f) eq d };

              // random approach not reliable enough as coded
              /*
              LIMIT := 10;
              found := false;
              count := 0;
              while (count lt LIMIT) and (not found) do
                  count +:= 1;
                  c := [ Random (k) : i in [1..#good] ];
                  s := &+ [ c[i] * good[i] : i in [1..#good] ];
                  r := s @@ f;
                  if Rank (r) eq d then
                     found := true;
                  end if;
             end while;
             */

             if not found then
                 "...no unit found!!";

             else
                 r := (&+ [ u[i] * good[i] : i in [1..#good] ]) @@ f;
                 mu_r := InsertBlock (r, Identity (ma), 1, 1);
                 isit, rbar := __IsPseudoIsometry (mu_r, VtenV, pi : Vgen := Vgen);
                 assert isit;
                 t := a * mu_r;
                 tbar := abar * rbar;
                 //"transporter test:", K2 * abar * rbar eq K1;
                 isit := IsPseudoIsometry (t, [X1, Y1], [X2, Y2]);
                 assert isit;

            end if;

         end if;
         
     end while;
     
     if not found then
         return false, _, _;
     end if;

     // SANITY CHECK: final + outer map
     g := C2^-1 * C_adj^-1 * t * C1;
     isit, gg := IsPseudoIsometry (g, pair1, pair2);
     assert isit;

return true, g, gg;

end function;




