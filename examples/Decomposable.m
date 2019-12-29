P<x, y> := PolynomialRing(GF(7), 2);
f := x*y;
G := Genus2Group(f);
G;
IsIndecomposable(G);
