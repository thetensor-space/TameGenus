TG_SG := [*G : G in SmallGroups(3^6) | IsTameGenusGroup(G)*];
#TG_SG;

G1 := [*G : G in TG_SG | Genus(G) eq 1*];
G2 := [*G : G in TG_SG | Genus(G) eq 2*];
#G1;
#G2;

for G in G1 do
    TGSignature(G);
end for;

for G in G2 do
    TGSignature(G);
end for;
