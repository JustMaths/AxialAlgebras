/*

We define an axet

*/
declare type Axet;

declare attributes Axet:
  axes,           // A GSet of the axes
  tau,            // A map from Ax \times T to G, where G = Group(Ax)
  Miyamoto_group, // The Miyamoto group on the axes
  tau_stabiliser; // The stabiliser of tau

intrinsic Information(Ax::Axet) -> List
  {
  Returns the information for printing.
  }
  return [* GroupName(MiyamotoGroup(Ax)), Join([ IntegerToString(#o) : o in Orbits(MiyamotoGroup(Ax), Axes(Ax))], "+") *];
end intrinsic;

intrinsic Print(Ax::Axet)
  {
  Prints an axet.
  }
  info := Information(Ax);
  printf "Axet for the group %o, on %o axes", info[1], info[2];
end intrinsic;
/* 

===========  Basic functions  ===========

*/
intrinsic TGroup(Ax::Axet) -> Grp
  {
  The T-group of an axet.
  }
  return Domain(Tau(Ax))[2];
end intrinsic

intrinsic Axes(Ax::Axet) -> GSet
  {
  The axes of an axet.
  }
  return Ax`axes;
end intrinsic;

intrinsic Tau(Ax::Axet) -> Map
  {
  The axes of an axet.
  }
  return Ax`tau;
end intrinsic;

intrinsic '#'(Ax::Axet) -> RngIntElt
  {
  The size of the axet.
  }
  return #Axes(Ax);
end intrinsic;

intrinsic Group(Ax::Axet) -> GrpPerm
  {
  The full group of an axet.
  }
  return Group(Axes(Ax));
end intrinsic;

intrinsic AxisSubgroup(Ax::Axet, x::.) -> GrpPerm
  {
  The axis subgroup of x.
  }
  require IsCoercible(Axes(Ax), x): "You have not given a valid axis.";
  tau := Tau(Ax);
  
  return sub< Group(Ax) | [ tau(x,t) : t in Component(Domain(tau), 2)]>;
end intrinsic;

intrinsic MiyamotoGroup(Ax::Axet) -> GrpPerm
  {
  The Miyamoto group of an axet.
  }
  if not assigned Ax`Miyamoto_group then
    Ax`Miyamoto_group := sub<Group(Ax) | TauImage(Tau(Ax))>;
  end if;
  return Ax`Miyamoto_group;
end intrinsic;

intrinsic Hash(Ax::Axet) -> RngIntElt
  {
  The hash value of an axet.
  }
  return Hash(<Group(Ax), Axes(Ax), Tau(Ax)>);
end intrinsic;
/* 

===========  Creation of GSets and axets  ===========

*/
intrinsic InvolutionGSets(G::GrpPerm) -> SeqEnum
  {
  Returns a sequence of GSets which correspond to the faithful action of G on a union of conjugacy classes of involutions and such that those involutions generate G.  We dedupe this for the action of the outer automorphism group of G.
  }
  class2 := {@ c[3] : c in Classes(G) | c[1] eq 2 @};

  orbs := {@ Orbit(G,x) : x in class2 @};
  // Two sets of involutions which are conjugate under an outer automorphism will produce the same posibilities for the shape.
 
  aut := AutomorphismGroup(G);
  autFP, FPmap := FPGroup(aut);
  out, out_map := OuterFPGroup(aut);
  outPerm, perm_map := PermutationGroup(out);

  elts_out := [ g@@perm_map@@out_map@FPmap : g in outPerm ];
  
  // We need to dedupe the set of all possible subsets of orbs for those which are conjugate under the outer automorphisms
  // At the same time, we check for generation of G
  
  all_invs := {@ @};
  for invs in {@ IndexedSet(x) : x in Subsets(Set(orbs)) | x ne {} @} do
    if sub<G | &join invs > ne G then
      continue;
    end if;
    if not exists(t){ f : f in elts_out | {@ GSet(G, o@f) : o in invs @} in all_invs } then
      Include(~all_invs, invs);
    end if;
  end for;

  all_GSets := [];
  for invs in all_invs do
    idems := &join invs;

    Ax := IndexedSet([1..#idems]);
    tau := map<Ax -> G | i :-> idems[i]>;
    AxxG := CartesianProduct(Ax, G);
    f := map< AxxG -> Ax | y :-> Position(idems,(y[1] @ tau)^y[2])>;
    Ax := GSet(G, Ax, f);
    if IsTrivial(ActionKernel(G,Ax)) then
      Include(~all_GSets, Ax);
    end if;
  end for;
  
  return Sort(all_GSets, func< x,y| #x-#y>);
end intrinsic;

intrinsic Axet(X::GSet, tau::Map: faithful:=true, image:=Group(X)) -> Axet
  {
  Builds the an axet.
  }
  require IsTauMap(X, Component(Domain(tau), 2), tau: faithful:=faithful, image:=image): "You have not given a valid tau-map.";
  
  Ax := New(MakeType("Axet"));
  Ax`axes := X;
  Ax`tau := tau;
  
  return Ax;
end intrinsic;
/*

======= Create new GSets and axets from old ones =======

*/
intrinsic Union(X1::GSet, X2::GSet) -> GSet
  {
  For two GSets X1 and X2 with the same action group, returns their union.
  }
  G := Group(X1);
  require G eq Group(X2): "The two GSets do not have the same action group.";
  X := IndexedSet([1..#X1+#X2]);
  XxG := CartesianProduct(X, G);
  f := map< XxG -> X | y :-> y[1] le #X1 select Image(y[2], X1, y[1]) else Image(y[2], X2, y[1]-#X1)+#X1>;
  return GSet(G, X, f);
end intrinsic;

intrinsic Union(Ax1::Axet, Ax2::Axet) -> Axet
  {
  For two axets with the same action group and same T group, returns their union.
  }
  T := Component(Domain(Tau(Ax1)), 2);
  require T eq Component(Domain(Tau(Ax2)), 2): "The two tau-maps do not have the same T group.";
  X := Union(Axes(Ax1), Axes(Ax2));
  n := #Axes(Ax1);
  
  XxT := CartesianProduct(X, T);
  tau := map<XxT -> Group(X) | p :-> p[1] le n select p@Tau(Ax1) else <p[1]-n, p[2]>@Tau(Ax2)>;
  
  return Axet(X, tau: faithful:=false, image:=false);
end intrinsic;

intrinsic Closure(Ax::Axet, Y::.) -> Axet, Map
  {
  Given a set Y of axes, returns their Miyamoto closure Z and an inclusion map Z \to X.
  }
  Y := Flat(< ISA(Type(y), MakeType("Set")) select Setseq(y) else y : y in Y>);
  X := Axes(Ax);
  require forall{y : y in Y | IsCoercible(X, y)}: "Not all elements are coercible into the axet.";

  H := sub<Group(Ax) | [ AxisSubgroup(Ax, y) : y in Y]>;
  Z := OrbitClosure(H, X, {@ y : y in Y@});
  
  tau := Tau(Ax);
  tau := map<CartesianProduct(Z, Domain(tau)[2]) -> H | p:-> p@tau>;
  
  return Axet(Z, tau: faithful:=false, image:=false), map<Z->X | i:->i>;
end intrinsic;

intrinsic SubConstructor(Ax::Axet, Y::.) -> Axet, Map
  {
  Given a set Y of axes, find their Miyamoto closure Z, and then takes the subaxet of Ax given by Z.  Also returns an inclusion map.
  }
  Z, inc := Closure(Ax, Y);
  Z_axes := Axes(Z);
  H := Stabiliser(Group(Ax), Axes(Ax), Z_axes);
  
  Z := GSet(H, Axes(Ax), Z_axes);
  tau := Tau(Ax);
  tau := map< CartesianProduct(Z_axes, Domain(tau)[2]) -> H | p:-> p@tau>;
  
  return Axet(Z_axes, tau: faithful:=false, image:=false), map<Z->Axes(Ax) | i:->i>;
end intrinsic;

intrinsic Core(Ax::Axet) -> Axet
  {
  The core of an axet.  That is, the set of axes X with the group acting being the Miyamoto group of the axet factored out by the kernel of the action.
  }
  G := Group(Ax);
  X := Axes(Ax);
  Miy := MiyamotoGroup(Ax);
  ker := ActionKernel(Miy, X);
  Q, quo := quo<Miy|ker>;
  
  Y := IndexedSet(X);
  YxQ := CartesianProduct(Y, Q);
  f := map< YxQ -> Y | y :-> Image(y[2]@@quo, X, y[1])>;
  Y := GSet(Q, Y, f);
  
  tau := map< CartesianProduct(Y, TGroup(Ax)) -> Q | p :-> p@Tau(Ax)@quo>;
  
  return Axet(Y, tau: faithful:=false, image:=false);
end intrinsic;
/*

======= Equality and isomorphism =======

*/
function GSetEq(X1, X2)
  return X1 eq X2 and ActionImage(Group(X1), X1) eq ActionImage(Group(X2), X2);
end function;

// Can improve this by using TauMapEq if it is slow
function MapEq(f, g)
  return Domain(f) eq Domain(g) and [ i@f : i in Domain(f)] eq [ i@g : i in Domain(g)];
end function;

intrinsic 'eq'(Ax1::Axet, Ax2::Axet) -> BoolElt
  {
  Equality of axets.
  }
  return GSetEq(Axes(Ax1), Axes(Ax2)) and MapEq(Tau(Ax1), Tau(Ax2));
end intrinsic;

intrinsic IsIsomorphic(X1::GSet, X2::GSet) -> BoolElt, Map, Map
  {
  Checks whether G1 and G2 are isomorphic and have isomorphic actions.  If so, returns the map phi:X1 -> X2 and isomorphism psi:G1 -> G2.
  }
  G1 := Group(X1);
  G2 := Group(X2);
  
  if #X1 ne #X2 or Order(G1) ne Order(G2) then
    return false, _, _;
  end if;
  
  // Find the isomorphism between G1 and G2
  so, psi := IsIsomorphic(G1, G2);
  if not so then return false, _, _; end if;
  
  // This is wasteful as we throw away the isomorphism just found above, but I can't see how to do it better
  
  // We need to make standard versions of both
  function StandardAction(X)
    Y := IndexedSet([1..#X]);
    H := Group(X);
    YxH := CartesianProduct(Y, H);
    f := map<YxH -> Y | y:-> Position(X, Image(y[2], X, X[y[1]]))>;
    return GSet(H, Y, f);
  end function;
  
  Y1 := StandardAction(X1);
  Y2 := StandardAction(X2);
  act1, GG1 := Action(G1, Y1);
  act2, GG2 := Action(G2, Y2);
  so, perm := IsConjugate(Sym(#X1), GG1, GG2);
  if not so then return false, _, _; end if;
  
  phi := map< X1 -> X2 | i:-> X2[Position(X1,i)^perm], j:-> X1[Position(X2,j)^(perm^-1)]>;
  psi := hom<G1 -> G2 | [<g,((g@act1)^perm)@@act2> : g in FewGenerators(G1)]>;
  
  assert2 forall{<i,g> : i in X1, g in Generators(G1) | Image(g,X1,i)@phi eq Image(g@psi, X2, i@phi)};
  
  return true, phi, psi;
end intrinsic;

intrinsic ActionNormaliser(X::GSet) -> GrpPerm
  {
  The normaliser of the action.
  }
  G := Group(X);
  GG := Stabiliser(Sym(X), Set(Orbits(G, X)));
  N := Normaliser(GG, ActionImage(G, X));
  
  return N;
end intrinsic;

intrinsic IsIsomorphic(Ax1::Axet, Ax2::Axet) -> BoolElt, Map, Map
  {
  Tests if Ax1 and Ax2 are isomorphic.  If so, it returns a pair, phi:X1 -> X2 and isomorphism psi:G1 -> G2 such that
  
  (i^g)@phi = (i@phi)^(g@psi) for all i in Ax1, g in G1 and
  
  tau1(i,t)^phi = tau2(i^phi, t) for all i in Ax1, t in T
  }
  T := TGroup(Ax1);
  require T eq TGroup(Ax2): "The two T-groups are not equal.";
  
  X1 := Axes(Ax1); G1 := Group(Ax1); tau1 := Tau(Ax1);
  X2 := Axes(Ax2); G2 := Group(Ax2); tau2 := Tau(Ax2);
  
  so, phi, psi:= IsIsomorphic(X1, X2);
  if not so then return false, _, _; end if;
  
  N := ActionNormaliser(X2);
  
  // We form the tau map for the conjugated X1
  X2xT := Domain(tau2);
  tau_adj := map<X2xT -> G2 | p:-> <p[1]@@phi, p[2]>@tau1@psi>;
  
  // We define a quick version of equality of maps
  orb_reps := {@ Representative(o) : o in Orbits(G2, X2)@};
  TauMapEq := function(f, g)
    return forall{i: i in orb_reps, t in Generators(T) | <i,t>@f eq <i,t>@g};
  end function;
    
  // The action on tau maps is
  // tau_n := tau(i^(n^-1))^n
  
  // But G2 doesn't act on the tau maps
  act2, GG2:= Action(G2, X2);
  trans := Transversal(N, GG2);
  
  so := exists(n){n : n in trans | TauMapEq(tau2, map< X2xT-> G2 |
                        p:-> ((<p[1]^(n^-1), p[2]>@tau_adj@act2)^n)@@act2>)};
  
  if not so then return false, _, _; end if;
  
  // We adjust phi by n
  
  phi := map< X1 -> X2 | i:-> (i@phi)^n, j:-> (j^(n^-1))@@phi>;
  assert2 TauMapEq(tau2, map< X2xT -> Group(X2) | p:-> <p[1]@@phi, p[2]>@tau1@psi>);
  
  return true, phi, psi;
end intrinsic;
/*

======= Tau maps =======

*/
/*

A function for sorting the tau maps, so we get a deterministic tau map

*/
function TauSort(f, g)
  X, T := Explode(Components(Domain(f)));
  G := Codomain(f);
  for x in [1..#X] do
    imf := [Eltseq(f(x,t)) : t in T];
    img := [Eltseq(g(x,t)) : t in T];
    // We have two sequences of permutations for the axis subgroups.
    so := exists(i){i : i in [1..#imf] | imf[i] ne img[i]};
    if not so then
      continue;
    elif imf[i] lt img[i] then
      return -1;
    else
      assert imf[i] gt img[i];
      return 1;
    end if;
  end for;
  return 0;
end function;

intrinsic TauImage(tau::Map) -> GrmPerm
  {
  The image of a tau map.
  }
  // NB magma doesn't support images for some domains.  This one seems not to work.
  Miy := sub< Codomain(tau) | [ p@tau : p in Domain(tau)]>;
  ReduceGenerators(~Miy);
  return Miy;
end intrinsic;

intrinsic IsTauMap(X::GSet, T::GrpPerm, tau::Map: faithful:=true, image:=Group(X)) -> BoolElt
  {
  Checks whether tau is a valid tau-map on XxT.
  
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  G := Group(X);
  ReduceGenerators(~G);
  if faithful then
    require IsFaithful(G, X): "The action is not faithful.";
  elif Type(image) eq GrpPerm and TauImage(tau) ne image then
    vprintf ParAxlAlg, 2: "The map does not have the required image.";
    return false;
  end if;
  
  tauX, tauT := Explode(Components(Domain(tau)));
  
  orb_reps := { t[2] : t in OrbitRepresentatives(ActionImage(G, X))};
  if tauX eq X and tauT eq T and TauImage(tau) subset Group(X) and
     forall{ <x, t1, t2, g> : x in orb_reps, t1,t2 in FewGenerators(T), g in FewGenerators(G) | 
        <x,t1>@tau in Stabiliser(G, X, x) and
        <x,t1*t2>@tau eq (<x,t1>@tau)*(<x,t2>@tau) and
        <Image(g,X,x),t1>@tau eq (<x,t1>@tau)^g} then
    return true;
  else
    return false;
  end if;
end intrinsic;

TauMapEq := function(orb_reps, T, f, g)
  return forall{i: i in orb_reps, t in FewGenerators(T) | <i,t>@f eq <i,t>@g};
end function;
  
intrinsic TauAction(X::GSet, tau_maps::SetIndx) -> GSet
  {
  Given a GSet X and a set of tau-maps on X, find the induced action on the tau maps.
  }
  if not IsEmpty(tau_maps) then
    T := Component(Domain(tau_maps[1]), 2);
    require forall{tau : tau in tau_maps | IsTauMap(X, T, tau: faithful:=false, image:=false)}: "The maps given are not tau-maps with the same domain";
  end if;
  
  XxT := CartesianProduct(X, T);
  G := Group(X);
  act, GG := Action(G, X);
  
  // The action on tau maps is
  // tau_n := tau(i^(n^-1))^n
  
  // It's just as fast to form the function and then calculate the image of orb_reps as it is to only calculate the images of orb_reps (as tested on orb_rep of size 3)
  act := function(tau, n)
    return map<XxT-> G | p:-> ((<p[1]^(n^-1), p[2]>@tau@act)^n)@@act >;
  end function;
  
  // tau-maps are defined by their action on orbit representatives.
  orb_reps := {@ Representative(o) : o in Orbits(G, X) @};
  orbxT := [ t : t in CartesianProduct(orb_reps, T)];
  
  // G doen't act on the tau-maps
  N := ActionNormaliser(X);
  trans := Transversal(N, GG);
  
  orb_images := {};
  all_tau_maps := [];
  
  for t in tau_maps, n in trans do
    tau := act(t, n);
    Im_tau := orbxT@tau;
    if not Im_tau in orb_images then
      Include(~orb_images, Im_tau);
      Append(~all_tau_maps, tau);
    end if;
  end for;
  all_tau_maps := IndexedSet(all_tau_maps);

  tau_return := function(f)
    assert exists(g){g : g in all_tau_maps | TauMapEq(orb_reps, T, f,g)};
    return g;
  end function;

  tausxN := CartesianProduct(all_tau_maps, N);
  f := map< tausxN -> all_tau_maps | y :-> tau_return(act(y[1], y[2])) >;
  Taus := GSet(N, all_tau_maps, f);
  
  return Taus;
end intrinsic;

intrinsic StabiliserOfTauMap(Ax::Axet: force_recompute:=false) -> GrpPerm
  {
  Returns the stabiliser of the tau-map.
  }
  if not assigned Ax`tau_stabiliser or force_recompute then
    T := TGroup(Ax);
    orb_reps := {@ Representative(o) : o in Orbits(Group(Ax), Axes(Ax)) @};
    
    Taus := TauAction(Axes(Ax), {@Tau(Ax)@});
    
    // There isn't equality for maps, so we must identify the map in Taus which is equal!
    assert exists(t){ t : t in Taus | TauMapEq(orb_reps, T, Tau(Ax), t)};
    Ax`tau_stabiliser := Stabiliser(Group(Taus), Taus, t);
  end if;
  
  return Ax`tau_stabiliser;
end intrinsic;

intrinsic TauMaps(X::GSet, T::GrpPerm: faithful := true, image := Group(X)) -> SeqEnum
  {
  Find all the tau-maps on XxT up to automorphism.  Returns a sequence of tuples < tau, stabiliser(tau)>.
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  G := Group(X);
  if faithful then
    require IsFaithful(G, X): "The action is not faithful";
  end if;
  XxT := CartesianProduct(X, T);
  // Check!!
  if #X eq 1 then
    return [map<XxT->G | i:->G!1>];
  end if;
  
  // returns all homomorphisms between T and H
  Tab, T_to_Tab := AbelianGroup(T);
  function HomSet(T, H)
    Hab, H_to_Hab := AbelianGroup(H);
    homs, homs_to_maps := Hom(Tab, Hab);
    return {@ T_to_Tab*(f@homs_to_maps)*H_to_Hab^-1 : f in homs @};
  end function;
  
  orb_reps := {@ o[2] : o in OrbitRepresentatives(ActionImage(G, X)) @};
  possibles := [ HomSet(T, Centre(Stabiliser(G, X, x))) : x in orb_reps];
  
  cart := [ c : c in CartesianProduct(possibles)];
  
  tau_maps := {@ @};
  
  function OrbitConjugator(x)
    assert exists(t){ <i,g> : i in [1..#orb_reps] | so
                      where so,g := IsConjugate(G, X, orb_reps[i], x)};
    return Explode(t);  
  end function;
  
  for poss in CartesianProduct(possibles) do
    tau := map< XxT -> G | p :-> (p[2]@poss[i])^g where i,g := OrbitConjugator(p[1])>;
    if Type(image) eq GrpPerm and TauImage(tau) ne image then
      continue;
    end if;
    Include(~tau_maps, tau);
  end for;
  
  if #tau_maps eq 0 then
    return [];
  end if;
  
  // We now wish to dedupe the set of tau maps using the automorphisms of Ax
  Taus := TauAction(X, tau_maps);
  N := Group(Taus);

  // We wish to get a deterministic algorithm, so we sort the tau-maps
  Taus_orbs := [ Sort(o, TauSort) : o in Orbits(N, Taus)];
  Taus_orb_reps := Sort([o[1] : o in Taus_orbs], TauSort);
  
  return [ <tau, Stabiliser(N, Taus, tau)> where tau := Taus_orb_reps[i]
              : i in [1..#Taus_orb_reps]];
end intrinsic;
/*

======= Loading and saving an Axet =======

*/
intrinsic AxetToList(Ax::Axet) -> MonStgElt
  {
  Transform an Axet into a List prior to serialisation as a JSON.
  }
  L := [* *];
  Append(~L, <"class", "Axet">);
  
  G := Group(Ax);
  X := Axes(Ax);
  tau := Tau(Ax);
  T := Component(Domain(tau), 2);
  ReduceGenerators(~T);
  Tgen := GeneratorsSequence(T);
  ReduceGenerators(~G);
  Ggen := GeneratorsSequence(G);
  act := Action(G, X);
  orb_reps := {@ o[1] : o in Orbits(G, X) @};
  
  Append(~L, <"GSet", [* [*g, g@act*] : g in Ggen *]>);
  Append(~L, <"T", [* t : t in Tgen*]>);
  Append(~L, <"tau", [* [* [* i, j *], <i,Tgen[j]>@tau *] : i in orb_reps, j in [1..#Tgen] *]>);
  
  return L;
end intrinsic;

intrinsic Axet(A::Assoc) -> Axet
  {
  Create an axet from an associative array.  We assume that the associative array represents the axet stored in json format.
  }
  keys := Keys(A);
  require "class" in keys and A["class"] eq "Axet": "The file given does not encode an axet.";
  
  gens := [Numbers(k[1]) : k in A["GSet"]];
  images := [Numbers(k[2]) : k in A["GSet"]];
  n := Max(gens[1]);
  G := PermutationGroup<n | gens>;
  m := Max(images[1]);
  act := hom<G -> Sym(m) | [<G!gens[i], Sym(m)!images[i]> : i in [1..#gens]]>;
  
  X := IndexedSet([1..m]);
  XxG := CartesianProduct(X, G);
  f := map<XxG -> X | y:-> y[1]^(y[2]@act)>;
  X := GSet(G, X, f);
  
  Tgens := [Numbers(k) : k in A["T"]];
  T := PermutationGroup<Max(Tgens[1]) | Tgens>;
  
  XxT := CartesianProduct(X, T);
  
  orb_reps := {@ p[1,1] : p in A["tau"] @};
  homs := [ hom<T->G | [ <Tgens[p[1,2]], G!Numbers(p[2])> : p in A["tau"] | p[1,1] eq orb_reps[i]]>
                : i in [1..#orb_reps] ];
  
  function OrbitConjugator(x)
    assert exists(t){ <i,g> : i in [1..#orb_reps] | so
                      where so,g := IsConjugate(G, X, orb_reps[i], x)};
    return Explode(t);  
  end function;
  
  tau := map< XxT -> G | p :-> (p[2]@homs[i])^g where i,g := OrbitConjugator(p[1])>;
  
  return Axet(X, tau: faithful:=false, image:=false);
end intrinsic;
