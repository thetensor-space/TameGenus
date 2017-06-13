/* 
    Copyright 2015--2017, Peter A. Brooksbank, Joshua Maglione, James B. Wilson.
    Distributed under GNU GPLv3.
*/



/*--- implementation of Ronyai's trick: finding a suitable translate ---*/

/*
   Input: 
      (1) Associative, unital k-algebra R (assume AlgGen type); 
      (2) Bases X, Y for k-subspaces of R
   Output: 
      r in R such that sp(X).r = sp(Y) (if such exists)

   Ultimately we wish to extend this to "substitution automorphisms"
   of R, and perhaps also to Galois automorphisms.
*/

__is_translate := function (R, X, Y)

     k := BaseRing (R);
     n := Dimension (R);
     t := #X;

     /* makes sure X and Y have equal length */
     if #X ne #Y then 
         return false, _;
     end if;

     /* write elements of X and Y as linear combinations of basis of R */
     alpha := [ Coordinates (R, X[i]) : i in [1..#X] ];
     beta  := [ Coordinates (R, Y[i]) : i in [1..#Y] ];

     /* build matrix */
     mat := KMatrixSpace (k, t*n, n + t^2)!0;
     for i in [1..t] do
         for d in [1..n] do
	    // create row (i-1)n + d
            for m in [1..n] do
               for j in [1..n] do
                  sjm := BasisProduct (R, j, m);
                  mat[(i-1)*n+d][m] +:= alpha[i][j] * sjm[d]; 
	       end for;
	    end for;
            for c in [1..t] do
		  mat[(i-1)*n+d][n+(i-1)*t+c] := -beta[c][d];
	    end for;
         end for;
     end for;

     /* solve the system of equations */
     mat := Transpose (mat);
     null := Nullspace (mat);
     if Dimension (null) eq 0 then
         return false, _;
     end if;

     /* project basis for <null> onto the first n coordinates and coerce into R */
     Rbas := [ ];
     for i in [1..Ngens (null)] do
         t := null.i;
         ri := &+ [ t[i] * R.i : i in [1..n] ];
         Append (~Rbas, ri);
     end for;

return true, Rbas;

end function;


