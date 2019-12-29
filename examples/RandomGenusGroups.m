G := TGRandomGroup(5^7, 8, 4);
#G eq 5^(7*(8 + 4));

Genus(G);

t := pCentralTensor(G);
t;
C := Centroid(t);
Dimension(C);
IsSimple(C);
