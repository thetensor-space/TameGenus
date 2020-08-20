P<x> := PolynomialRing(GF(9));
f := x^3*(x-1)^2*(x-2);
G := Genus2Group(f);
#G eq 9^(2*6 + 2);

S := TGSignature(G);
S[4];
