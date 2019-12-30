G := SmallGroup(3^6, 440);
#DerivedSubgroup(G) eq 3^2;
IsElementaryAbelian(DerivedSubgroup(G));
Genus(G);

H := SmallGroup(3^6, 469);
#DerivedSubgroup(H) eq 3^2;
IsElementaryAbelian(DerivedSubgroup(H));
Genus(H);

s := pCentralTensor(G);
t := pCentralTensor(H);
C_G := Centroid(s);
C_H := Centroid(t);
C_G;
C_H;

Dimension(C_G);
Dimension(C_H);
WedderburnDecomposition(C_G);
IsSimple(C_H);
