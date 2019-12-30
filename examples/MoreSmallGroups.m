TG_SG := SmallGroupProcess(3^7, IsTameGenusGroup);

repeat
    G := Current(TG_SG);
    _, ID := CurrentLabel(TG_SG);
    print "Small group ID:", ID;
    TGSignature(G);
    Advance(~TG_SG);
until IsEmpty(TG_SG);
