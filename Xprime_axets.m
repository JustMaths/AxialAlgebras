/*

X' axets

*/
AttachSpec("ParAxlAlg.spec");
C := CyclicGroup(2);

// X'(3)
G := sub<Sym(3) | (2,3)>;

X := GSet(G);
Taus := TauMaps(X, C);
assert #Taus eq 1;

tau, stab := Explode(Taus[1]);
Ax := Axet(X, tau);

// X'(6)
G := sub<Sym(6) | (3,5)(4,6), (1,2)(3,4), (1,2)(5,6)>;

X := GSet(G);
Taus := TauMaps(X, C);
assert #Taus eq 1;

tau, stab := Explode(Taus[1]);
Ax := Axet(X, tau);

// X'(9)
G := sub<Sym(9) | (2, 3)(4, 5)(6, 9)(7, 8), (1, 3)(5, 9)(6, 8)>;

X := GSet(G);
Taus := TauMaps(X, C);
assert #Taus eq 2;
assert exists(tau){ t[1] : t in Taus | <1,C.1>@t[1] ne <2,C.1>@t[1]};

Ax := Axet(X, tau);

assert #sub<Ax | 1,6> eq 3;

// X'(9)
G := DihedralGroup(6);
class2 := {@ c[3] : c in Classes(G) | c[1] eq 2 @};
X := {@1,2,3@};
invs := Orbit(G, class2[3]);
XxG := CartesianProduct(X, G);
f := map<XxG -> X | x:-> Position(invs, invs[x[1]]^x[2])>;
X1 := GSet(G, X, f);

X2 := GSet(G);

X := Union(X1, X2);


