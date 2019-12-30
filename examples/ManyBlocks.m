blocks := [1, 1, 1, 2, 2, 3, 3, 5, 6];
G := RandomGenus2Group(9, blocks);
#G eq 9^(&+blocks + 2);

TGSignature(G);
