/*
    Experiment D tests isomorphism of two isomorphic genus 2 groups. All groups 
  have order p^10. We test all primes from 3 to 257, and we compare the Pfaffian
  method against the adjoint-tensor method. We run 5 tests for each method for 
  each prime. We run this on 5 cores; each core doing one test for each method.
*/

/* Parameters */
file_time := "/scratch/maglione/Genus2Data/ExpD_TimeData";
Core_Num := 1;

// =============================================================================
// =============================================================================

/* Preliminaries */
load "run";
file_time cat:= IntegerToString(Core_Num);
primes := Remove(PrimesUpTo(257),1);
__GetIsomorphicGroups := function(p)
  G := RandomGroupSG( p, 8, 2 : Exponentp := true );
  T := pCentralTensor(G,1,1);
  X := Matrix(Random(GL(8,p)));
  Z := Matrix(Random(GL(2,p)));
  Forms := SystemOfForms(T);
  Forms := [ X*F*Transpose(X) : F in Forms ];
  Forms := [ &+[ Z[j][i]*Forms[j] : j in [1,2] ] : i in [1,2] ];
  S := Tensor( Forms, 2, 1 );
  H := HeisenbergGroup( S );
  return G, H;
end function;



/* Test */
for p in primes do

  G,H := __GetIsomorphicGroups(p);
  assert #G eq #H;

  tt := Cputime();
  bool1 := IsIsomorphicSG(G, H : Method:=1, Constructive:=true );
  adjten_time := Cputime(tt);
  assert bool;

  tt := Cputime();
  bool2 := IsIsomorphicSG(G, H : Method:=2, Constructive:=true );
  pfaff_time := Cputime(tt);
  assert bool;

  delete G,H;
  mem := GetMaximumMemoryUsage();
  mem := RealField(4)!(mem/1024/1000);
  
  PrintFile(file_time, Sprintf( "%o;%o,%o", p, adjten_time, pfaff_time ) );

  Sprintf( "Core: %o\nPrime: %o\nAdj-ten: %o s\nPfaffian: %o s\nMem: %o MB\nSeed: %o\n",\
    Core_Num, p, adjten_time, pfaff_time, mem, GetSeed() );
  
end for;
