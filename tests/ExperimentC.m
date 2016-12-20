/*
    Experiment C tests if two genus 2 groups are isomorphic. For a genus two 
  group G, construct its adjoint algebra, A, and construct cotensor space given 
  by the exterior square over A. Run through random 2-dimensional subcotensor 
  spaces until the associated tensor is not pseudo-isometric to the tensor of G.
  Run through tests to see if we can determine nonisomorphism another way. All
  groups have order 3^d, for d even between 8 and 20. We use 3 cores, and each
  core will run 1 test for each d.
*/

/* Parameters */
file := "Genus2Data/ExpD_Data";
Core_Num := 1;

// =============================================================================
// =============================================================================

/* Preliminaries */
//load "run";
load "Dropbox/MagmaPackages/SmallGenus/prelims.m";
dims := [6..18];
__GetNonisomorphicGroups := function(p,d)
  q := p^1;
  k := GF (q);
  V := VectorSpace (k, d);
  MA := MatrixAlgebra (k, d);
  repeat 
    /* choose random sloped pair */
    repeat
      M := Random (MA);
      F1 := M - Transpose (M);
    until Rank (F1) eq d;
    N := Random (MA);
    G1 := N - Transpose (N);

    /* form the tensor over its adjoint ring */
    Rgen := G1 * F1^-1;
    A := AdjointAlgebra ([F1, G1]);
    X := [ < A.i , A.i @ A`Star > : i in [1..Ngens (A)] ];
    isit, W, pi := __tensor_over_adj (X, Rgen);
    assert isit;

    /* form the system of forms for the tensor product ... a bit clunky */
    m := Dimension (W);
    PHI := [ MA!0 : i in [1..m] ];
    for i in [1..d] do
      for j in [1..d] do
        wij := TensorProduct (V.i, V.j) @ pi;
        for l in [1..m] do
          PHI[l][i][j] := wij[l];
        end for; 
      end for;
    end for;

    /* choose a random 2-dimensional (sloped) subspace */
    MS := KMatrixSpace (k, d, d);
    PHI := [ MS!PHI[l] : l in [1..m] ];
    //U := KMatrixSpaceWithBasis (PHI);
    U := sub< MS | PHI >;
    repeat
      F2 := Matrix (Random (U));
    until Rank (F2) eq d;
    G2 := Matrix (Random (U));

    G := HeisenbergGroup(Tensor([F1, G1],2,1));
    H := HeisenbergGroup(Tensor([F2, G2],2,1));
  until (#G eq #H) and (not IsIsomorphicSG(G,H));
  return G,H;
end function;

/* Test */
for d in dims do
  G,H := __GetNonisomorphicGroups(3, d);
end for;
