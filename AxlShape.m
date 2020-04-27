/*

We define admissibility of tau-maps and a shape object

*/
// Set this to the relative directory of where the library is
library_location := "../AxialAlgebras/library";

declare type AxlShape: Axet;

declare attributes AxlShape:
  fusion_law,     // A FusLaw
  shape;          // Shape given as a sequence of tuples <S, type>, where S is a subset of axes and type is the type of 2-generated subgroup glued in on those axes

import "Axet.m": GSetEq, MapEq;

intrinsic Information(Sh::AxShape) -> List
  {
  Returns the information for printing.
  }
  return [* GroupName(MiyamotoGroup(Sh)), Join([ IntegerToString(#o) : o in Orbits(MiyamotoGroup(Sh), Axes(Sh))], "+"), &cat[ t[2] : t in Shape(Sh)] *];
end intrinsic;

intrinsic Print(Sh::AxlShape)
  {
  Prints a shape.
  }
  info := Information(Sh);
  printf "Shape for the group %o, on %o axes, of shape %o", info[1], info[2], info[3];
end intrinsic;

// Do I even need this??
intrinsic ShapePrint(L::SetIndx[AxlShape]) -> MonStgElt
  {
  Prints a shape.
  }
  return [<info[1], info[2], info[3]> where info := Information(Sh) : Sh in L];
end intrinsic;
/* 

===========  Basic functions  ===========

*/
intrinsic FusionLaw(Sh::AxlShape) -> FusLaw
  {
  The fusion law of a shape.
  }
  return Sh`fusion_law;
end intrinsic

intrinsic Shape(Sh::AxlShape) -> SeqEnum
  {
  A map from pairs of axes to the shape.
  }
  // NOT YET IMPLEMENTED
end intrinsic;

intrinsic Hash(Sh::AxlShape) -> RngIntElt
  {
  The hash value of a shape.
  }
  return Hash(<FusionLaw(Sh), Group(Sh), Axes(Sh), Tau(Sh), Shape(Sh)>);
end intrinsic;
/*

======= Admissibility of tau-maps =======

*/
// This function reads the fusion law info and returns it.
/*
For a fusion law FL, in its directory Directory(FL), there is a file called info.json
It encodes the following properties:

 - class - "Fusion Law Information"
 
 - fusion_law - Directory(FL)
 
 - admissible - A function to determine admissibility
 
 - undirected_shape_graph - a BoolElt giving whether the shape graph is undirected or not
 
 - complete_basic_algebras - a BoolElt on whether there is a complete set of 2-generated algebras
 
 - subalgebras - an Assoc with keys being the 2-gen algebra names and values being a list of tuples [subalg_name, axes]
*/
function GetFusionLawInfo(FL)
  filename := Sprintf("%o/%o/info.json", library_location, Directory(FL));
  
  string := Read(filename);
  // remove any end of line characters that magma tends to add
  string := &cat Split(string, "\\\n");
  info := ParseJSON(string);
  info["admissible"] := function(X, tau)
    return eval(info["admissible"]);
  end function;
  return info;
end function;

intrinsic IsAdmissibleTauMap(X::GSet, tau::Map, FL::FusLaw: faithful := true, image:=Group(X)) -> BoolElt
  {
  Is the tau-map tau an admissible tau-map for the given fusion law.  Currently only works with the Monster fusion law.
  }
  G := Group(X);
  T := Component(Domain(tau), 2);
  so := IsTauMap(X, T, tau: faithful:=faithful, image:=image);
  if not so then return false; end if;
  
  info := GetFusionLawInfo(FL);
  IsAdmissible := info["admissible"];
  return IsAdmissible(X, tau);
end intrinsic;

intrinsic HasAdmissibleTauMap(Ax::Axet, FL::FusLaw: faithful := true, image:=Group(Ax)) -> BoolElt
  {
  "
  }
  return IsAdmissibleTauMap(Axes(Ax), Tau(Ax), FL: faithful := faithful, image:=image);
end intrinsic;

intrinsic IsMonsterAdmissibleTauMap(X::GSet, tau::Map: faithful:=true, image:=Group(X)) -> BoolElt
  {
  Is the given tau-map is admissible for the Monster fusion law (or other similar laws).
  
  Specifically, this checks whether T has order 2 (or 1 if |X| = 1) and for any distinct pair a,b in X, the orbits of D_\{a,b\} := <tau_a, \tau_b> on a and b are either disjoint and have the same order 1,2, or 3; or are the same and have order 3, or 5.  It does not check whether the Miyamoto group is G.
  
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  return IsAdmissibleTauMap(X, tau, MonsterFusionLaw(): faithful := faithful, image:=image);
end intrinsic;

intrinsic HasMonsterAdmissibleTauMap(Ax::Axet: faithful := true) -> BoolElt
  {
  "
  }
  return IsAdmissibleTauMap(Axes(Ax), Tau(Ax), MonsterFusionLaw(): faithful := faithful, image:=image);
end intrinsic;

intrinsic AdmissibleTauMaps(X::GSet, FL::FusLaw: faithful := true, image := Group(X)) -> SeqEnum
  {
  Find all the addmissible tau-maps for the given fusion law up to automorphism.  Returns a sequence of tuples < tau, stabiliser(tau)>.  Currently only works with the Monster fusion law.
  
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  taus := TauMaps(X, CyclicGroup(2): faithful := faithful, image := image);
  
  return [ t : t in taus | IsAdmissibleTauMap(X, t[1], FL: faithful := faithful, image := image)];
end intrinsic;

intrinsic MonsterAdmissibleTauMaps(X::GSet: faithful := true, image := Group(X)) -> SeqEnum
  {
  Find all the tau-maps which are admissible for the Monster fusion law (or other similar laws) up to automorphism.  Returns a sequence of tuples < tau, stabiliser(tau)>.
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  taus := TauMaps(X, CyclicGroup(2): faithful := faithful, image := image);
  
  return [ t : t in taus |
            IsAdmissibleTauMap(X, t[1], MonsterFusionLaw(): faithful := faithful, image := image)];
end intrinsic;
/* 

===========  Creation of shapes  ===========

*/
intrinsic Shape(Ax::Axet, FL::FusLaw, shape::SeqEnum) -> AxlShape
  {
  Builds the shape of an axet.  NB no attempt is made to check the validity of the labels of the edges in the shape.
  }
  require IsIsomorphic(Grading(FL), TGroup(Ax)): "T is not isomorphic to the grading group.";
  require forall{ t : t in shape | t[1] subset Axes(Ax) and Type(t[2]) eq MonStgElt }: "You have not given a valid shape.";
  
  Sh := New(AxlShape);
  Sh`fusion_law := FL;
  Sh`axes := Axes(Ax);
  Sh`tau := Tau(Ax);
  Sh`shape := shape;
  
  return Sh;
end intrinsic;

intrinsic Shape(L::List) -> AxlShape
  {
  Builds the shape object.
  }
  require #L eq 4: "You have not given a valid shape input.";
  Ax, tau, shape, FL := Explode(L);
  return Shape(Ax, tau, shape, FL);
end intrinsic;

intrinsic Shape(X::GSet, tau::Map, shape::SeqEnum, FL::FusLaw: faithful:=true, image:=Group(X)) -> AxlShape
  {
  Builds the shape object.
  }
  so, iso := IsIsomorphic(Grading(FL), Components(Domain(tau))[2]);
  require so: "T is not isomorphic to the grading group.";
  require IsTauMap(X, Component(Domain(tau), 2), tau: faithful:=faithful, image:=image): "You have not given a valid tau-map.";
  require forall{ t : t in shape | t[1] subset X and Type(t[2]) eq MonStgElt }: "You have not given a valid shape.";

  Sh := New(AxlShape);
  Sh`fusion_law := FL;  
  Sh`axes := X;
  Sh`tau := tau;
  Sh`shape := shape;
  
  return Sh;
end intrinsic;
/*

======= Create new axets and shapes from old ones =======

*/
intrinsic 'join'(Sh1::AxlShape, Sh2::AxlShape) -> AxlShape
  {
  
  }
  // NOT YET IMPLEMENTED
  end intrinsic;

intrinsic Axet(Sh::AxlShape) -> Axet
  {
  The underlying axet for a shape.
  }
  Ax := New(MakeType("Axet"));
  Ax`axes := Axes(Sh);
  Ax`tau := Tau(Sh);
  
  return Ax;
end intrinsic;
/*

======= Equality and isomorphism =======

*/
intrinsic 'eq'(S::AxlShape, T::AxlShape) -> BoolElt
  {
  Equality of shapes.
  }
  return FusionLaw(S) eq FusionLaw(T) and GSetEq(Axes(S), Axes(T)) and MapEq(Tau(S), Tau(T)) and Shape(S) eq Shape(T);
end intrinsic;

intrinsic IsIsomorphic(Sh1::AxlShape, Sh2::AxlShape) -> BoolElt, GrpPermElt, Map
  {
  Tests if Sh1 and Sh2 are isomorphic.  If so, it returns a pair, perm in Sym(|Sh1|) and phi:G1->G2 such that
  
  (i^g)^perm = (i^perm)^(g@phi) for all i in Sh1, g in G1 and
  
  tau1(i,t)^perm = tau2(i^perm, t) for all i in Ax1, t in T
  
  such that perm maps shape1 onto shape2.
  }
  if #Axes(Sh1) ne #Axes(Sh2) or {*sh[2] : sh in Shape(Sh1)*} ne {*sh[2] : sh in Shape(Sh2)*} then
    return false, _, _;
  end if;
  
  so, perm, phi := IsIsomorphic(Axet(Sh1), Axet(Sh2));
  if not so then return false, _, _; end if;
  
  tau2 := Tau(Sh2);
  Taus := TauAction(Axes(Sh2), {@tau2@});
  stab := Stabiliser(Group(Taus), Taus, tau2);
  
  shape2 := Shape(Sh2);
  shape_orbs2 := [ Orbit(Group(Sh2), Axes(Sh2), sh[1]) : sh in shape2 ];
  
  orbmember := function(S);
    assert exists(i){i : i in [1..#shape_orbs2] | S in shape_orbs2[i]};
    return i;
  end function;
  
  so := exists(h){h : h in stab | forall{sh : sh in Shape(Sh1) | sh[2] eq shape2[orbmember(sh[1]^(perm*h))  , 2] }};
  if not so then
    return false, _, _;
  end if;
  
  perm := perm*h;
  assert2 MapEq(tau2, map<Domain(tau2) -> Codomain(tau2) | p:-> <p[1]^(perm^-1), p[2]>@Tau(Sh1)@phi>);
  
  return true, perm, phi;
end intrinsic;
/*

======= Shapes =======

*/
function SubalgebraOrb(Ax, S)
  D := sub<MiyamotoGroup(Ax) | [AxisSubgroup(Ax, x) : x in S]>;
  return &join[ Orbit(D, Axes(Ax), x) : x in S];
end function;

intrinsic ShapeGraph(Ax::Axet) -> GrphDir
  {
  Returns the shape graph.  It has vertices labelled by pairs \{a,b\} of distinct elements of orbits of Ax x Ax and a directed edge \{a,b\} to \{c,d\} when \{a,b\} dominates \{c,d\}.
  }
  G := Group(Ax);
  X := Axes(Ax);
  
  pairs := GSet(G,X,{ {@i,j@} : i,j in X | i ne j});
  pairs_orb_reps := OrbitRepresentatives(ActionImage(G, pairs));
  verts := [ o[2] : o in pairs_orb_reps ];
  
  // Now we need to find the domination edges
  edges := [];
  subalgs := [ SubalgebraOrb(Ax, o) : o in verts];
  Sort(~subalgs, func<x,y|#x-#y>, ~perm); // Sort smallest first
  verts := PermuteSequence(verts, perm);
  
  for i in [#verts..1 by -1] do
    // Find the subsets of orb up to conjugacy
    // NB verts is ordered by size, so we need only search in
    subsets := {@ o : S in Subsets(Set(subalgs[i]), 2) | so 
              where so := exists(o){ o : o in verts[1..i] | IsConjugate(G, X, o, IndexedSet(S))}@};
    subsets diff:= {@ verts[i]@};
    edges cat:= [ [ verts[i], o] : o in subsets];
  end for;
  
  return Digraph< Set(verts) | edges>;  
end intrinsic;
/*

======= Shapes =======

*/
intrinsic Shapes(Ax::Axet, FL::FusLaw) -> IndxSet
  {
  Returns the set of shapes for the axet Ax.
  }
  
  require HasMonsterAdmissibleTauMap(Ax): "The axet does not have a Monster-admissible tau-map.";
  
  Gr := ShapeGraph(Ax);
  
  info := GetFusionLawInfo(FL);
  // This gives us the information about the subalgebras of the fusion law
  
  if info["undirected_shape_graph"] then
    
  else
    require false: "Undirected shape graphs are not currently implemented.";
  end if;
  
  // NOT YET IMPLEMENTED
end intrinsic;

intrinsic MonsterShapes(G::GrpPerm) -> IndxSet
  {
  Builds all possible faithful actions of G on unions of involutions, all tau-maps on these where the Miyamoto group is G and return all shapes on these.
  }
  // NOT YET IMPLEMENTED
end intrinsic;

intrinsic Stabiliser(Sh::AxlShape) -> GrpPerm
  {
  The stabiliser of a given shape.
  }
  // NOT YET IMPLEMENTED
end intrinsic;





