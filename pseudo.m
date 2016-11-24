/* 
   Given a nondegenerate bimap of genus 2 (represented by a <pair> of
   alternating forms), return generators for its pseudo-isometry group.
*/ 

__G2PseudoIsometryGroupNondegenerate := function (pair)

     if __is_sloped (pair[1], pair[2]) then
          return true, __PseudoIsometryGroupSlopedPair (pair[1], pair[2]);
     end if;

     k := BaseRing (pair[1]);
     d := Nrows (pair[1]);
     V := VectorSpace (k, d);

tt := Cputime ();
     C, dims := PerpDecomposition (pair);
"   [__G2PIGN] time for perp decomposition", Cputime (tt);
     npair := [ C * pair[j] * Transpose (C) : j in [1,2] ];
     sloped_basis := [ ];
     flat_bases := < >;
     pos := 1;
     for i in [1..#dims] do
          res_pair := [ ExtractBlock (npair[j], pos, pos, dims[i], dims[i]) : j in [1,2] ];
          if __is_sloped (res_pair[1], res_pair[2]) then
              sloped_basis cat:= [ V.(pos+l-1) : l in [1..dims[i]] ];
          else
              Append (~flat_bases, [V.(pos+l-1) : l in [1..dims[i]] ]);
          end if;
          pos +:= dims[i];
     end for;
     
     if #flat_bases eq 0 then
     "   [__G2PIGN] THIS CASE NOT DEALT WITH YET";
         return false, _;
     end if;

                 /*--- COMMENT ---*/

     /*
         It's rare that this case comes up.
         The way forward -- if we wish to address it using adjoint-tensor -- 
         is to always work with the perp-indecomposables. 
         We have a fixed basis for GL(2,p), and testing for pseudo-isometry 
         on indecomposable i gives a coset x_i H_i of "outer" 
         pseudo-isometries that work.
         (In the case of a flat indecomposable, we get all of GL(2,p).)
         Now we test for pseudo-isometry by seeing if the intersection
         of cosets is non-empty.
     */

     /* see if it's all flat */
     FLAT := (#sloped_basis eq 0);

     /*  Find the first basis change exhibiting basic perp decomp. */
     basis := [ ];
     for i in [1..#flat_bases] do
         basis cat:= flat_bases[i];
     end for;
     basis cat:= sloped_basis;
     C1 := Matrix (basis) * C;
     F := C1 * pair[1] * Transpose (C1);
     G := C1 * pair[2] * Transpose (C1);
     
     /* 
        The second basis change simultaneously transforms 
        each flat component to its standard form.
     */
     pos := 1;
     blocks := < >;
     for i in [1..#flat_bases] do
         mi := #flat_bases[i];
         Fi := ExtractBlock (F, pos, pos, mi, mi);
         Gi := ExtractBlock (G, pos, pos, mi, mi);
         pos +:= mi;
         Di := __TransformFIPair (Fi, Gi);
         Append (~blocks, Di);
     end for;
     dsl := #sloped_basis;
     Append (~blocks, Identity (MatrixAlgebra (k, dsl)));
     C2 := DiagonalJoin (blocks);
     F := C2 * F * Transpose (C2);
     G := C2 * G * Transpose (C2);
     
     C := C2 * C1;
     
     /* 
        Find the pseudo-isometry group of the sloped part,
        together with its GL(2,k) image relative to the basis F, G.
     */
     if (not FLAT) then
          Fsl := ExtractBlock (F, pos, pos, dsl, dsl);
          Gsl := ExtractBlock (G, pos, pos, dsl, dsl);
          
     if Nrows (Fsl) le 2 then
          "   [__G2PIGN] need to handle this case separately ... failure for now";
          return false, _;
     end if;

     // ONE OF THESE COULD BE ZERO ... NEED TO HANDLE THIS CASE SEPARATELY
          H := __PseudoIsometryGroupSlopedPair (Fsl, Gsl);
          H_im_gens := [ ];
          gl2 := GL (2, k);
          MS := KMatrixSpace (k, dsl, dsl);
          MS := KMatrixSpaceWithBasis ([ MS!Fsl , MS!Gsl ]);
          for i in [1..Ngens (H)] do
              h := H.i;
              h_im := Matrix ([ Coordinates (MS, MS!(h*Fsl*Transpose(h))),
                            Coordinates (MS, MS!(h*Gsl*Transpose(h))) ]);
              Append (~H_im_gens, gl2!h_im);
          end for; 
     
          /* sloped sanity check */
          good := true;
          for i in [1..Ngens (H)] do
              h := H.i;
              hh := H_im_gens[i];
              good and:=
           (h * Fsl * Transpose (h) eq (hh[1][1] * Fsl + hh[1][2] * Gsl)) and
           (h * Gsl * Transpose (h) eq (hh[2][1] * Fsl + hh[2][2] * Gsl));
          end for;

     end if;
     
tt := Cputime ();
     /* 
        Construct the pseudo-isometry groups of the flat parts,
        and embed them diagonally.
     */
     if #flat_bases gt 0 then
     
          gen_blocks := < 
              __PseudoIsometryGroupStandardFIPair (k, (#flat_bases[i] - 1) div 2) :
                   i in [1..#flat_bases]
                   >;
          assert forall { i : i in [1..#gen_blocks] | #(gen_blocks[i]) eq 3 };
          gens := [ DiagonalJoin (< gen_blocks[i][j] : i in [1..#gen_blocks] >) :
                        j in [1,2,3] ];
                    
          /* first sanity check */
          m := Nrows (gens[1]);
          Ffl := ExtractBlock (F, 1, 1, m, m);
          Gfl := ExtractBlock (G, 1, 1, m, m);
          assert (gens[1] * Ffl * Transpose (gens[1]) eq PrimitiveElement (k) * Ffl) and
           (gens[1] * Gfl * Transpose (gens[1]) eq Gfl) and
           (gens[2] * Ffl * Transpose (gens[2]) eq Gfl) and
           (gens[2] * Gfl * Transpose (gens[2]) eq Ffl) and
           (gens[3] * Ffl * Transpose (gens[3]) eq (Ffl+Gfl)) and
           (gens[3] * Gfl * Transpose (gens[3]) eq Gfl);
                    
         /* Set up isomorphism with GL(2,k) with nice generators. */
         trgens := [ Transpose (gens[i]) : i in [1..#gens] ]; 
         flat_PSEUDO := sub < GL (Nrows (gens[1]), k) | trgens >;
         a := PrimitiveElement (k);
         x1 := GL (2, k)![a,0,0,1];
         x2 := GL (2, k)![0,1,1,0];
         x3 := GL (2, k)![1,1,0,1];
         flat_gl2 := sub < GL (2, k) | [ x1 , x2 , x3 ] >;
         RandomSchreier (flat_PSEUDO);
         RandomSchreier (flat_gl2);
         assert #flat_PSEUDO eq #flat_gl2;
         psi := hom < flat_gl2 -> flat_PSEUDO | trgens >;

            assert
            (x1 @ psi eq Transpose (gens[1])) and
            (x2 @ psi eq Transpose (gens[2])) and
            (x3 @ psi eq Transpose (gens[3]));

         if (not FLAT) then
             good := true;
             for i in [1..#H_im_gens] do
                 hh := H_im_gens[i];
                 h := Transpose (hh @ psi);
                 good and:=
               (h * Ffl * Transpose (h) eq (hh[1][1] * Ffl + hh[1][2] * Gfl)) and
               (h * Gfl * Transpose (h) eq (hh[2][1] * Ffl + hh[2][2] * Gfl));
             end for;
         end if;
      
         if (not FLAT) then
             /* 
                Find elements of flat_PSEUDO that map to the gens
                of the outer pseudo-isometry group of the sloped part.
             */
             Hflat_gens := [ Transpose ((H_im_gens[i]) @ psi) : 
                                              i in [1..#H_im_gens] ];
                    
             /* Diagonally adjoin gens of H to get full pseudo-isometry group. */
             PSEUDO_gens := [ DiagonalJoin (Hflat_gens[i], H.i) : i in [1..Ngens (H)] ];
             
         else
         
             PSEUDO_gens := [ Transpose (flat_PSEUDO.i) : 
                                 i in [1..Ngens (flat_PSEUDO)] ];
         
         end if;

     else

          PSEUDO_gens := [ H.i : i in [1..Ngens (H)] ];
 
     end if;
     
"   [__G2PIGN] handled sloped pert in time", Cputime (tt);
     
     /* conjugate back */
tt := Cputime ();
     PSEUDO_gens := [ C^-1 * PSEUDO_gens[i] * C : i in [1..#PSEUDO_gens] ];
     PSEUDO := sub < GL (d, k) | PSEUDO_gens >;
       
     /* final sanity check */
/*
     MS := KMatrixSpace (k, d, d);
     MS := KMatrixSpaceWithBasis ([ MS!(pair[1]) , MS!(pair[2]) ]);
assert          forall { i : i in [1..Ngens (PSEUDO)] | forall { j : j in [1,2] | 
             ((PSEUDO.i) * pair[j] * Transpose (PSEUDO.i) in MS) } };
"   [__G2PIGN] final sanity check in time", Cputime (tt);
*/

return true, PSEUDO;

end function;


/* 
   Given an arbitrary bimap of genus 2 (represented by a <pair> of
   alternating forms), return generators for its pseudo-isometry group.
*/ 


G2PseudoIsometryGroup := function (pair)
ss := Cputime ();

     assert #pair eq 2;

     k := BaseRing (pair[1]);
     d := Nrows (pair[1]);   
     
     /* chop out the radical */  
tt := Cputime ();
     rad := &meet [ Nullspace (M) : M in pair ];
     bas := Basis (Complement (VectorSpace (k, d), rad)) cat Basis (rad);
     C := Matrix (bas);
     npair := [ C * pair[i] * Transpose (C) : i in [1..#pair] ];
     m := d - Dimension (rad);
     npair := [ ExtractBlock (npair[i], 1, 1, m, m) : i in [1..#npair] ];
"[G2PIG] time to chop out radical:", Cputime (tt);
 
tt := Cputime ();    
     /* find the pseudo-isometry group of the nondegenerate part */
     flag, H := __G2PseudoIsometryGroupNondegenerate (npair);
     if not flag then
          return false, _;
     end if;
"[G2PIG] total time for nondegenerate bimap:", Cputime (tt);
     
     /* embed into bigger group */
     PSEUDO_gens := [ DiagonalJoin (H.i, Identity (MatrixAlgebra (k, Dimension (rad)))) :
                      i in [1..Ngens (H)] ];
     PSEUDO_gens := [ C^-1 * PSEUDO_gens[i] * C : i in [1..#PSEUDO_gens] ];
     
     /* throw in the isometries */
tt := Cputime ();
     ISOM := IsometryGroup (pair : DisplayStructure := false);
"[G2PIG] time to build isometries:", Cputime (tt);
tt := Cputime ();
     PSEUDO := sub < GL (d, k) | PSEUDO_gens cat [ ISOM.i : i in [1..Ngens (ISOM)] ] >;
     MS := KMatrixSpace (k, d, d);
     MS := KMatrixSpaceWithBasis ([ MS!(pair[1]) , MS!(pair[2]) ]);
     assert          forall { i : i in [1..Ngens (PSEUDO)] | forall { j : j in [1,2] | 
             ((PSEUDO.i) * pair[j] * Transpose (PSEUDO.i) in MS) } };
"[G2PIG] time for final sanity check:", Cputime (tt);

"[G2PIG] total time:", Cputime (ss);
     
return true, PSEUDO;     
     
end function;


__G2IsPseudoIsometricNondegenerate := function (pair1, pair2)


end function;



G2IsPseudoIsometric := function (pair1, pair2)


end function;
