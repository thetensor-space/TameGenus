T := RandomTensor(GF(7),[6,6,2]);
T := AlternatingTensor(T);
G := HeisenbergGroupPC(T);

G;

Genus(G);

TGSignature(G);

