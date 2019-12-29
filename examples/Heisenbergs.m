G := RandomGenus1Group(81, 2, 0);
#G eq 81^(2*2 + 1);

D := DerivedSubgroup(G);
IsElementaryAbelian(D);
#D eq 3^4;

Genus(G);
