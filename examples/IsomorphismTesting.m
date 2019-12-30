f := RandomIrreduciblePolynomial(GF(67), 3);
g := RandomIrreduciblePolynomial(GF(67), 3);
f, g;
G := Genus2Group(f);
H := Genus2Group(g);

SetVerbose("TameGenus", 1);
isomorphic, phi := TGIsIsomorphic(G, H);

isomorphic;
phi;

isomorphic, phi2 := TGIsIsomorphic(G, H : Method := 2);
phi2;
