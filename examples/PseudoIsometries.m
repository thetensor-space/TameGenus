M := RandomMatrix(GF(3), 50, 50);
N := RandomMatrix(GF(3), 50, 50);
Forms1 := [M - Transpose(M), N - Transpose(N)];
s := Tensor(Forms1, 2, 1);
s;
IsAlternating(s);


X := Random(GL(50, 3));
Y := Random(GL(2, 3));
Maps := [*X, X, Y*];
H := Homotopism(Maps, CohomotopismCategory(3));
t := s @ H;
t;
s eq t;

pisometric, Phi := TGIsPseudoIsometric(s, t : Cent := false);
pisometric;
Phi.0;
