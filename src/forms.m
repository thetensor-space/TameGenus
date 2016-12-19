// melange of functions relating to forms ... not all are really needed


/* compute the k-space of d x d skew-symmetric forms */
SpaceOfAlternatingForms := function (d, K)
     MS := KMatrixSpace (K, d, d);
     Z := MS!0;
     basis := [ ];
     for i in [1..d-1] do
         for j in [i+1..d] do
	    X := Z;
            X[i][j] := 1;
            X[j][i] := -1;
            Append (~basis, X);
	 end for;
     end for;
return KMatrixSpaceWithBasis (basis);
end function;


MyOrthogonalComplement := function (V, U, F)
     k := BaseRing (V);
     M := Matrix (k, Dimension (V), Dimension (U), 
			            [ 0 : i in [1..Dimension (V) * Dimension (U)] ]);
     for s in [1..Dimension (V)] do
	     for t in [1..Dimension (U)] do
		     M[s][t] := InnerProduct (V.s * F, U.t);
         end for;
     end for;
return Nullspace (M);
end function;

/* 
   given a form matrix <F> and a subspace <U> return the matrix 
   representing the restriction of <F> to <U>, relative to the
   stored basis for <U>.
*/
__restrict_form := function (F, U)
     B := Basis (U);
     F_res := Matrix ([ [ InnerProduct (B[i] * F, B[j]) : j in [1..#B] ] : 
              i in [1..#B] ]);
return MatrixAlgebra (BaseRing (U), Dimension (U))!F_res;
end function;


/* <y> is a d x d matrix and <MS> a space of matrices */
__transformation_on_forms := function (y, MS)
     ims := [ ];
     for i in [1..Ngens (MS)] do
         X := MS.i;
         Xy := y * X * Transpose (y); 
         imXy := Coordinates (MS, MS!Xy);
         Append (~ims, imXy);
     end for;
return Matrix (ims);
end function;


/* 
  useful function to construct the action of GL(d,k)
  on the space of d x d skey-symmetric forms
*/
GLActionOnForms :=  function (d, K)
     G := GL (d, K);
     MS := SpaceOfAlternatingForms (d, K);
     gens := [ __transformation_on_forms (Transpose (G.i), MS) : 
				   i in [1..Ngens (G)] ];
     n := Degree (Parent (gens[1]));
     H := sub < GL (n, K) | gens >;
     RandomSchreier (H);
     RandomSchreier (G);
     phi := hom < G -> H | gens >;
     inverse := hom < H -> G | h :-> Transpose (h @@ phi) >;
return G, H, inverse;
end function;


/* use this function to test pseudo-isometry group code */
StabilisesFormSpace := function (H, S)
return forall { i : i in [1..Ngens (H)] |
          forall { j : j in [1..Ngens (S)] |
              H.i * S.j * Transpose (H.i) in S } };
end function;


/* returns true if and only if <H> is a subgroup of Isom(<S>) */
CentralisesFormSpace := function (H, S)
return forall { i : i in [1..Ngens (H)] |
          forall { j : j in [1..Ngens (S)] |
              H.i * S.j * Transpose (H.i) eq S.j } };
end function;


/*
  given a subgroup <H> of GL(d,k) and a space of
  alternating forms <U> compute the orbit of <U>
  under the action

  F -> h^t F h
  
  of <H>^tr; we assume that <H> is small enough to be listed.
*/

__orbit_of_form_space := function (H, U)
     orb := { sub < Generic (U) | [ Transpose (h) * U.i * h :
                    i in [1..Ngens (U)] ] > : h in H };
return [ x : x in orb ];
end function;


/*
  given an element <h> of a group <H> and an <H>-orbit
  <orb> of form spaces, compute the permutation induced
  by <h> on <orb> relative to the given ordering.
*/

__permutation_of_form_spaces := function (h, orb)
     n := #orb;
     image := [ ];
     for i in [1..n] do
         U := orb[i];
         W := sub < Generic (U) | 
               [ Transpose (h) * U.i * h : i in [1..Ngens (U)] ] >;
         assert exists (j){ l : l in [1..n] | W eq orb[l] };
         Append (~image, j);
     end for;
return SymmetricGroup (n)!image;
end function;

/*
  Given a subgroup <H> of GL(d,k) and a space of
  alternating forms <U> compute the subgroup of <H>
  that stabilises <U> under the action F -> h F h^t
*/

StabiliserOfFormSpace := function (H, U)

     /* to get an action, swap <H> for its transpose */
     Htr := sub < Generic (H) | 
                  [ Transpose (H.i) : i in [1..Ngens (H)] ] >;

     /* compute the <Htr>-orbit of <U> */
     orb := __orbit_of_form_space (Htr, U);

     /* next compute the perm gp induced by <Htr> on <orb> */
     n := #orb;
     sym := SymmetricGroup (n);
     gens := [ __permutation_of_form_spaces (Htr.i, orb) : 
                                     i in [1..Ngens (Htr)] ];
     permHtr := sub < sym | gens >;
     phi := hom < Htr -> permHtr | gens >;
     K := Kernel (phi);

     /* compute the stabiliser of <U> in the perm action */
     i := Position (orb, U);
     permHtr_stab := Stabiliser (permHtr, i);
     
     /* pull back to <Htr> and correct the action */
     Htr_stab := permHtr_stab @@ phi;
     stab_gens_tr := [ K.i : i in [1..Ngens (K)] ] cat
                     [ Htr_stab.i : i in [1..Ngens (Htr_stab)] ];
     stab_gens := [ Transpose (stab_gens_tr[i]) : 
                                   i in [1..#stab_gens_tr] ];     

return sub < Generic (H) | stab_gens >;
end function;

is_refinement := function (C, D)
     isit := true;
     dist := Set ( [ D[i][j] : 
                     i in [1..Nrows (D)], j in [1..Ncols (D)] ]);
     for d in dist do
         monoD := { <i, j> : 
                  i in [1..Nrows (D)], j in [1..Ncols (D)] |
                       D[i][j] eq d };
         colC := { C[x[1],x[2]] : x in monoD };
         isit and:= (#colC eq 1);
     end for;
return isit;
end function;

PGLonFormSpace := function (U)

     W := KMatrixSpaceWithBasis ([ U.i : i in [1..Ngens (U)] ]);
     points := { sub < U | u > : u in U | not u eq 0 };
     points := [ P : P in points ];
     n := #points;
     t := Dimension (U);
     k := BaseRing (U);
     V := VectorSpace (k, t);
     gl := GL (t, k);

     pgl_gens := [ ];
     sym := SymmetricGroup (n);
     for i in [1..Ngens (gl)] do
         x := gl.i;
         image := [ ];
         for j in [1..n] do
            F := points[j].1;
            c := Coordinates (W, F);
            v := (V!c) * x;
            G := &+ [ v[l] * W.l : l in [1..t] ];
            assert exists (imj){ r : r in [1..n] | 
                                 sub < U | G > eq points[r] };
            Append (~image, imj);
         end for;
         Append (~pgl_gens, sym!image);
     end for;
       
return sub < sym | pgl_gens >, points;  

end function;
