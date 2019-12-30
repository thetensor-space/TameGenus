p := 541;
G := RandomGenus2Group(p, [29]);
#G eq p^(29 + 2);
A := TGAutomorphismGroup(G);
IsDivisibleBy(#A, #GL(2, p));

#A eq (p - 1)*p^28 * (p^2 - 1)*(p^2 - p) * p^(29*2);
