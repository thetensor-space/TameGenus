G := RandomGenus2Group(3, [4, 6, 10]);
#G eq 3^(4 + 6 + 10 + 2);
Genus(G);


SetVerbose("TameGenus", 1);
A := TGAutomorphismGroup(G);

