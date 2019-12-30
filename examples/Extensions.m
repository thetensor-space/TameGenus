G := RandomGenus2Group(3^2, [6]);
t := pCentralTensor(G);
t;
Genus(t);

PI := TGPseudoIsometryGroup(t);
Random(PI);
Factorization(#PI);

s := TensorOverCentroid(t);
s;
PI_C := TGPseudoIsometryGroup(s);
Random(PI_C);
Factorization(#PI_C);
