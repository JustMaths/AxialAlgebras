/*

We define an axet

*/
declare type Axet;

declare attributes Axet:
  axes,           // A GSet of the axes
  tau,            // A map from Ax \times T to G, where G = Group(Ax)
  Miyamoto_group; // The Miyamoto group on the axes

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
  require IsCoercible(Ax, x): "You have not given a valid axis.";
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
    f := map< AxxG -> Ax | y :-> Position(idems,((y[1] @ tau)^y[2]))>;
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
intrinsic 'join'(X1::GSet, X2::GSet) -> GSet
  {
  
  }
  // NOT YET IMPLEMENTED
end intrinsic;

intrinsic 'join'(Ax1::Axet, Ax2::Axet) -> Axet
  {
  
  }
  // NOT YET IMPLEMENTED
end intrinsic;
/*

======= Equality and isomorphism =======

*/
function GSetEq(X1, X2)
  return X1 eq X2 and ActionImage(Group(X1), X1) eq ActionImage(Group(X2), X2);
end function;

function MapEq(f, g)
  return Domain(f) eq Domain(g) and [ i@f : i in Domain(f)] eq [ i@g : i in Domain(g)];
end function;

intrinsic 'eq'(S::Axet, T::Axet) -> BoolElt
  {
  Equality of axets.
  }
  return GSetEq(Axes(S), Axes(T)) and MapEq(Tau(S), Tau(T));
end intrinsic;

intrinsic IsIsomorphic(X1::GSet, X2::GSet) -> BoolElt, GrpPerm, Map
  {
  Checks whether G1 and G2 are isomorphic and have isomorphic actions.  If so, returns the permutataion X1 -> X2 and isomorphism phi:G1 -> G2.
  }
  G1 := Group(X1);
  G2 := Group(X2);
  
  if #X1 ne #X2 or Order(G1) ne Order(G2) then
    return false, _, _;
  end if;
  
  // Find the isomorphism between G1 and G2
  so, phi := IsIsomorphic(G1, G2);
  if not so then return false, _, _; end if;
  
  //Now find the equivalence between the action of G1 on X1 and G1@phi on X2
  
  act1, GG1 := Action(G1, X1);
  act2, GG2 := Action(G1@phi, X2);
  so, perm := IsConjugate(Sym(#X1), GG1, GG2);
  if not so then return false, _, _; end if;
  
  assert2 forall{<i,g> : i in X1, g in Generators(G1) | Image(g,X1,i)^perm eq Image(g@phi, X2, i^perm)};
  
  return true, perm, phi;
end intrinsic;

intrinsic ActionNormaliser(X::GSet) -> GrpPerm
  {
  The normaliser of the action.
  }
  G := Group(X);
  GG := Stabiliser(Sym(#X), Set(Orbits(G, X)));
  N := Normaliser(GG, ActionImage(G, X));
  
  return N;
end intrinsic;

intrinsic IsIsomorphic(Ax1::Axet, Ax2::Axet) -> BoolElt, GrpPermElt, Map
  {
  Tests if Ax1 and Ax2 are isomorphic.  If so, it returns a pair, perm in Sym(|Ax1|) and phi:G1->G2 such that
  
  (i^g)^perm = (i^perm)^(g@phi) for all i in Ax1, g in G1 and
  
  tau1(i,t)^perm = tau2(i^perm, t) for all i in Ax1, t in T
  }
  T := TGroup(Ax1);
  require T eq TGroup(Ax2): "The two T-groups are not equal.";
  
  X1 := Axes(Ax1); G1 := Group(Ax1); tau1 := Tau(Ax1);
  X2 := Axes(Ax2); G2 := Group(Ax2); tau2 := Tau(Ax2);
  
  so, perm, phi:= IsIsomorphic(X1, X2);
  if not so then return false, _, _; end if;
  
  N := ActionNormaliser(X2);
  
  // We form the tau map for the conjugated X1
  X2xT := Domain(tau2);
  tau_adj := map<X2xT -> G2 | p:-> <p[1]^(perm^-1), p[2]>@tau1@phi>;
  
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
  
  // We adjust the permutation by n
  
  perm := perm*n;
  assert2 TauMapEq(tau2, map< X2xT -> Group(X2) | p:-> <p[1]^(perm^-1), p[2]>@tau1@phi>);
  
  return true, perm, phi;
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
  
  TauMapEq := function(f, g)
    return forall{i: i in orb_reps, t in Generators(T) | <i,t>@f eq <i,t>@g};
  end function;

  tau_return := function(f)
    assert exists(g){g : g in all_tau_maps | TauMapEq(f,g)};
    return g;
  end function;

  tausxN := CartesianProduct(all_tau_maps, N);
  f := map< tausxN -> all_tau_maps | y :-> tau_return(act(y[1], y[2])) >;
  Taus := GSet(N, all_tau_maps, f);
  
  return Taus;
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

======= Admissibility of tau-maps =======

*/
intrinsic IsAdmissibleTauMap(X::GSet, tau::Map, FL::FusLaw: faithful := true) -> BoolElt
  {
  Is the tau-map tau an admissible tau-map for the given fusion law.  Currently only works with the Monster fusion law.
  }
  // Add more fusion laws here when we get them
  require FL eq MonsterFusionLaw(): "Currently only works with the Monster fusion law.";
  return IsMonsterAdmissibleTauMap(X, tau: faithful := faithful);
end intrinsic;

intrinsic HasAdmissibleTauMap(Ax::Axet, FL::FusLaw: faithful := true) -> BoolElt
  {
  "
  }
  return IsAdmissibleTauMap(Axes(Ax), Tau(Ax), FL: faithful := faithful);
end intrinsic;

intrinsic IsMonsterAdmissibleTauMap(X::GSet, tau::Map: faithful:=true, image:=Group(X)) -> BoolElt
  {
  Is the given tau-map is admissible for the Monster fusion law (or other similar laws).
  
  Specifically, this checks whether T has order 2 (or 1 if |X| = 1) and for any distinct pair a,b in X, the orbits of D_\{a,b\} := <tau_a, \tau_b> on a and b are either disjoint and have the same order 1,2, or 3; or are the same and have order 3, or 5.  It does not check whether the Miyamoto group is G.
  
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  G := Group(X);
  T := Component(Domain(tau), 2);
  if #X eq 1 and Order(T) le 2 then
    return true;
  elif not Order(T) eq 2 then
    vprint ParAxlAlg, 2: "T does not have order equal two.";
    return false;
  end if;
  
  so := IsTauMap(X, T, tau: faithful:=faithful, image:=image);
  if not so then return false; end if;
  
  // Check for a pair a,b, |a^D| = |b^D| and other size properties
  pairs_orb_reps := [ o[2] : o in OrbitRepresentatives(
                       ActionImage(G, GSet(G,X,{ {@i,j@} : j in [i+1..#X], i in [1..#X]})))];
  
  for pair in pairs_orb_reps do
    D := sub<G | tau(pair[1], T.1), tau(pair[2], T.1)>;
    o1 := Orbit(D, X, pair[1]);
    o2 := Orbit(D, X, pair[2]);
    if #o1 ne #o2 then
      return false;
    elif o1 eq o2 then
      if #o1 notin {3,5} then
        return false;
      end if;
    else
      if #o1 notin {1,2,3} then
        return false;
      end if;
    end if;
  end for;
  
  return true; 
end intrinsic;

intrinsic HasMonsterAdmissibleTauMap(Ax::Axet: faithful := true) -> BoolElt
  {
  "
  }
  return IsMonsterAdmissibleTauMap(Axes(Ax), Tau(Ax): faithful := faithful);
end intrinsic;

intrinsic AdmissibleTauMaps(X::GSet, FL::FusLaw: faithful := true, image := Group(X)) -> SeqEnum
  {
  Find all the addmissible tau-maps for the given fusion law up to automorphism.  Returns a sequence of tuples < tau, stabiliser(tau)>.  Currently only works with the Monster fusion law.
  
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  // Add more fusion laws here when we get them
  require FL eq MonsterFusionLaw(): "Currently only works with the Monster fusion law.";
  return MonsterAdmissibleTauMaps(X: faithful:=faithful, image:=image);
end intrinsic;

intrinsic MonsterAdmissibleTauMaps(X::GSet: faithful := true, image := Group(X)) -> SeqEnum
  {
  Find all the tau-maps which are admissible for the Monster fusion law (or other similar laws) up to automorphism.  Returns a sequence of tuples < tau, stabiliser(tau)>.
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  taus := TauMaps(X, CyclicGroup(2): faithful := faithful, image := image);
  
  return [ t : t in taus | IsMonsterAdmissibleTauMap(X, t[1]: faithful := faithful, image := image)];

  // What is below is only almost the same as the above, except it rules out possible a few cases initially, and only dedupes for the group action later.
  /*
  G := Group(X);
  if faithful then
    require IsFaithful(G, X): "The action is not faithful";
  end if;
  
  T := CyclicGroup(2);
  XxT := CartesianProduct(X, T);
  if #X eq 1 and IsFaithful(Group(X), X) then
      return [map<XxT->G | i:->G!1>];
        // Do I need a special case here ???
  end if;
  
  // returns all homomorphisms between T and H
  Tab, T_to_Tab := AbelianGroup(T);
  function HomSet(T, H)
    Hab, H_to_Hab := AbelianGroup(H);
    homs, homs_to_maps := Hom(Tab, Hab);
    return {@ T_to_Tab*(f@homs_to_maps)*H_to_Hab^-1 : f in homs @};
  end function;
  
  // For the Monster, the orbits of D_{a,b} = < \tau_a, \tau_b > on a and b have the same size.
  // So, if a^G = a, then b^D = b for all b.  In particular, \tau_a in in the kernel K of the action.
  // It is also in Z(G_a) = Z(G).
  
  orb_reps := OrbitRepresentatives(ActionImage(G, X));
  possibles := [ o[1] eq 1 select HomSet(T, Centre(G) meet ActionKernel(G, X))
                   else HomSet(T, Centre(Stabiliser(G, X, o[2]))) : o in orb_reps];
  
  cart := [ c : c in CartesianProduct(possibles)];
  
  tau_maps := {@ @};
  pairs_orbs_reps := [ o[2] : o in OrbitRepresentatives(
                        ActionImage(G, GSet(G,X,{ {@i,j@} : j in [i+1..#X], i in [1..#X]})))];
  
  function OrbitConjugator(x)
    assert exists(t){ <i,g> : i in [1..#orb_reps] | so
                      where so,g := IsConjugate(G, X, orb_reps[i,2], x)}
    return Explode(t);  
  end function;
  
  for poss in CartesianProduct(possibles) do
    tau := map< XxT -> G | p :-> (p[2]@poss[i])^g where i,g := OrbitConjugator(p[1])>;
    if Type(image) eq GrpPerm and TauImage(tau) ne image then
      continue;
    end if;
    
    // We verify it is admissible
    for pair in pairs_orb_reps do
      D := sub<G | tau(pair[1], T.1), tau(pair[2], T.1)>;
      o1 := Orbit(D, X, pair[1]);
      o2 := Orbit(D, X, pair[2]);
      if #o1 ne #o2 then
        continue poss;
      elif o1 eq o2 then
        if #o1 notin {3,5} then
          continue poss;
        end if;
      else
        if #o1 notin {1,2,3} then
          continue poss;
        end if;
      end if;
      end for;
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
  */
end intrinsic;
