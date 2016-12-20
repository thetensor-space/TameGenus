/*
    Experiment A tests isomorphism of two isomorphic genus 2 groups. All groups 
  have order 5^(d+2). We test all even d between 4 and max_slope and all odd d
  between 3 and max_flat. We run 3 tests for each odd d and 10 tests for each 
  even d. We record the timing and the orders of the blocks. We run this 
  experiment on 8 cores: the first 5 cores will run 2 tests for every even d, 
  and the remaining 3 will run 1 test for every odd d.
*/

/* Parameters */
max_flat := 211;
max_slope := 254;
file_time := "ExpA_TimeData";
file_block := "ExpA_BlockData";
Core_Num := 1;

// =============================================================================
// =============================================================================

/* Preliminaries */
load "run";
file_time cat:= IntegerToString(Core_Num);
file_block cat:= IntegerToString(Core_Num);
tests := (Core_Num le 5) select 2 else 1;
dims := (Core_Num le 5) 
        select [i : i in [4..max_slope] | IsEven(i) ] 
        else [i : i in [3..max_flat] | IsOdd(i) ];
__GetIsomorphicGroups := function(d)
  G := RandomGroupSG( 5, d, 2 : Exponentp := true );
  T := pCentralTensor(G,1,1);
  X := Matrix(Random(GL(d,5)));
  Z := Matrix(Random(GL(2,5)));
  Forms := SystemOfForms(T);
  Forms := [ X*F*Transpose(X) : F in Forms ];
  Forms := [ &+[ Z[j][i]*Forms[j] : j in [1,2] ] : i in [1,2] ];
  S := Tensor( Forms, 2, 1 );
  H := HeisenbergGroup( S );
  return G, H;
end function;



/* Test */
for d in dims do
  for i in [1..tests] do 

    G,H := __GetIsomorphicGroups(d);
    tt := Cputime();
    bool, _, blocks := IsIsomorphicSG(G, H);
    timing := Cputime(tt);
    assert bool;
    delete G,H;
    mem := GetMaximumMemoryUsage();
    mem := RealField(4)!(mem/1024/1000);
    
    PrintFile(file, Sprintf( "%o,%o", d, timing ) );
    PrintFile(file, Sprintf( "<%o,%o>", d, blocks ) );

    if tests eq 2 then
      Sprintf( "Dim: %o-%o", d, i );
    else
      Sprintf( "Dim: %o", d );
    end if;
    Sprintf( "Time: %o s\nBlocks: %o\nMem: %o MB", timing, blocks, mem );
    
  end for;
end for;
