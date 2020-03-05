--univariate divison algorithm
divAlg = (f,g) -> (
    q := 0;
    r := f;
    a := first degree g;
    while r!=0 and first degree g <= first degree r do (
                b := first degree r;
                q = q+leadCoefficient(r)/leadCoefficient(g)*x^(b-a);
                r = r-leadCoefficient(r)/leadCoefficient(g)*x^(b-a)*g;
                );
{q,r})

--checks if one monomial x divides a monomial y
--takes a tuple of exponents for x and y
monomialDivides = (x,y) -> (
    divides := true;
    for i from 0 to (#x -1) do (
        if x#i > y#i then(
            divides = false;
        );
    );
divides)

--multivariate divison algorithm
mDivAlg = (g,F) -> (
    R := ring g;
    s := #F;
    r := 0;
    A := mutableMatrix(R,1,s);
    p := g;
    i := 0;
    f := 0;
    fexp := 0;
    pexp := 0;
    divOccured := false;
    while p != 0 do (
        i = 0;
        divOccured = false;
        while (i < s)  and (divOccured == false) do (
            f = F#(i);
            fexp = exponents f;
            pexp = exponents p;
            if monomialDivides(fexp#0,pexp#0) == true then (
                A_(0,i) = A_(0,i) + sub((leadTerm p / leadTerm f), R);
                p = p - sub((leadTerm p / leadTerm f), R)*f;
                divOccured = true;
                )
            else i = i + 1
            );
            if divOccured == false then (
            r = r + leadTerm p;
            p = p - leadTerm p;
            ) else continue
        );
        --need better printing setup, output looks bad
    J := {};
    for i from 0 to s-1 do(
        J = append(J,A_(0,i))
    );
{J,r})

--calculates the lcm for two monomials f and g
monomialLCM = (f,g) -> (
    R := ring f;
    A := exponents f;
    B := exponents g;
    X := for i from 0 to (#A#0 - 1) list max(A#0#i,B#0#i);
    S := first entries vars R;
    l := 1;
    for i from 0 to #S -1 do(
        l = l * S#i ^ (X#i);
    );
l)

--calculates s-polynomial for f and g
sPoly = (f,g) -> (
    R := ring f;
    l1 = leadTerm f;
    l2 = leadTerm g;
    l = monomialLCM(l1,l2);
    s = sub((l / leadTerm f)*f - (l / leadTerm g)*g,R);
s)

--applies buchberger's algorithm to a generating set F
buchberger = F -> (
    --initialization of vars
    G := F;
    G' := {};
    f := 0;
    g := 0;
    s := 0;
    a := 0;
    p := 0;
    lenP := 0;
    P = {};
    for i from 0 to #G-2 do(
        for j from i+1 to #G-1 do (
            P = append(P,{G#i,G#j})
        );
    );
    --buchberger algorithm
    while G != G' do(
        G' = G;
        lenP = #P-1;
        for i from 0 to lenP do(
            p = P#0;
            f = p#0;
            g = p#1;
            s = sPoly(f,g);
            a = (mDivAlg(s,G))#1;
            if a == 0 then continue else (
                for i from 0 to #G-1 do(
                    P = append(P,{G#i, a});
                ); 
                G = append(G,a)
            );
            P = for n from 1 to #P-1 list P#n
        );
    );
G)