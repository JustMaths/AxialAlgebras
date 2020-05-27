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

intrinsic Information(Sh::AxlShape) -> List
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

// Do we want this to be a map??  Probably!
intrinsic Shape(Sh::AxlShape) -> SeqEnum
  {
  A map from pairs of axes to the shape.
  }
  return Sh`shape;
end intrinsic;

intrinsic Hash(Sh::AxlShape) -> RngIntElt
  {
  The hash value of a shape.
  }
  return Hash(<FusionLaw(Sh), Group(Sh), Axes(Sh), Tau(Sh), Sh`shape>);
end intrinsic;
/*

======= Admissibility of tau-maps =======

*/
// This function reads the fusion law info and returns it.
/*
For a fusion law FL, in its directory Directory(FL), there is a file called info.json
It encodes the following properties:

 - class - "Fusion law information"
 
 - fusion_law - Directory(FL)
 
 - admissible - A function to determine admissibility
 
 - undirected_shape_graph - a BoolElt giving whether the shape graph is undirected or not
 
 - complete_basic_algebras - a BoolElt on whether there is a complete set of 2-generated algebras
 
 - subalgebras - an Assoc with keys being the 2-gen algebra names and values being a list of tuples [subalg_name, axes]
*/
intrinsic GetFusionLawInformation(FL::FusLaw) -> Assoc
  {
  Returns the fusion law information.
  }
  filename := Sprintf("%o/%o/info.json", library_location, Directory(FL));
  
  string := Read(filename);
  // remove any end of line characters that magma tends to add
  string := &cat Split(string, "\\\n");
  info := ParseJSON(string);
  
  require "class" in Keys(info) and info["class"] eq "Fusion law information" and info["fusion_law"] eq "Monster_1,4_1,32": "The file given does not encode the correct fusion law information.";
  
  info["admissible"] := function(X, tau)
    return eval(info["admissible"]);
  end function;
  
  basics := Keys(info["basic_algebras"]);
  require basics eq Keys(info["subalgebras"]): "The list of 2-generated algebras do not match the list of subalgebras for the 2-generated algebras.";
  for k in basics do
    info["basic_algebras"][k] := Axet(info["basic_algebras"][k]);
    info["subalgebras"][k] := AssociativeArray([* <kk, [ IndexedSet(S) : S in Numbers(info["subalgebras"][k,kk])]> : kk in Keys(info["subalgebras"][k]) *]);
  end for;
  
  return info;
end intrinsic;

intrinsic IsAdmissibleTauMap(X::GSet, tau::Map, FL::FusLaw: faithful:=true, image:=Group(X)) -> BoolElt
  {
  Is the tau-map tau an admissible tau-map for the given fusion law.  Currently only works with the Monster fusion law.
  }
  G := Group(X);
  T := Component(Domain(tau), 2);
  so := IsTauMap(X, T, tau: faithful:=faithful, image:=image);
  if not so then return false; end if;
  
  info := GetFusionLawInformation(FL);
  IsAdmissible := info["admissible"];
  return IsAdmissible(X, tau);
end intrinsic;

intrinsic HasAdmissibleTauMap(Ax::Axet, FL::FusLaw: faithful:=true, image:=Group(Ax)) -> BoolElt
  {
  "
  }
  return IsAdmissibleTauMap(Axes(Ax), Tau(Ax), FL: faithful:=faithful, image:=image);
end intrinsic;

intrinsic IsMonsterAdmissibleTauMap(X::GSet, tau::Map: faithful:=true, image:=Group(X)) -> BoolElt
  {
  Is the given tau-map is admissible for the Monster fusion law (or other similar laws).
  
  Specifically, this checks whether T has order 2 (or 1 if |X| = 1) and for any distinct pair a,b in X, the orbits of D_\{a,b\} := <tau_a, \tau_b> on a and b are either disjoint and have the same order 1,2, or 3; or are the same and have order 3, or 5.  It does not check whether the Miyamoto group is G.
  
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  return IsAdmissibleTauMap(X, tau, MonsterFusionLaw(): faithful := faithful, image:=image);
end intrinsic;

intrinsic HasMonsterAdmissibleTauMap(Ax::Axet: faithful:=true, image:=Group(Ax)) -> BoolElt
  {
  "
  }
  return IsAdmissibleTauMap(Axes(Ax), Tau(Ax), MonsterFusionLaw(): faithful := faithful, image:=image);
end intrinsic;

intrinsic AdmissibleTauMaps(X::GSet, FL::FusLaw: faithful:=true, image:=Group(X)) -> SeqEnum
  {
  Find all the addmissible tau-maps for the given fusion law up to automorphism.  Returns a sequence of tuples < tau, stabiliser(tau)>.  Currently only works with the Monster fusion law.
  
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  taus := TauMaps(X, CyclicGroup(2): faithful:=faithful, image:=image);
  
  return [ t : t in taus | IsAdmissibleTauMap(X, t[1], FL: faithful:=faithful, image:=image)];
end intrinsic;

intrinsic MonsterAdmissibleTauMaps(X::GSet: faithful:=true, image:=Group(X)) -> SeqEnum
  {
  Find all the tau-maps which are admissible for the Monster fusion law (or other similar laws) up to automorphism.  Returns a sequence of tuples < tau, stabiliser(tau)>.
  Optional parameters: faithful to require the action is faithful, image can be either a group, or false.  If false, there is no restriction on the Image of the tau map, if it is a group, we require the tau map to have this image.
  }
  taus := TauMaps(X, CyclicGroup(2): faithful:=faithful, image:=image);
  
  return [ t : t in taus |
            IsAdmissibleTauMap(X, t[1], MonsterFusionLaw(): faithful:=faithful, image:=image)];
end intrinsic;
/* 

===========  Creation of shapes  ===========

*/
intrinsic Shape(Ax::Axet, FL::FusLaw, shape::SetIndx) -> AxlShape
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
  
  so, phi, psi := IsIsomorphic(Axet(Sh1), Axet(Sh2));
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
  
  so := exists(h){h : h in stab | forall{sh : sh in Shape(Sh1) | sh[2] eq shape2[orbmember(sh[1]@phi^h), 2] }};
  if not so then
    return false, _, _;
  end if;
  
  phi := map< Axes(Sh1) -> Axes(Sh2) | i:-> (i@phi)^h, j:-> (j^(h^-1))@@phi>;
  assert2 MapEq(tau2, map<Domain(tau2) -> Codomain(tau2) | p:-> <p[1]@@phi, p[2]>@Tau(Sh1)@psi>);
  
  return true, phi, psi;
end intrinsic;
/*

======= Shapes =======

*/
function SubalgebraOrb(Ax, S)
  D := sub<MiyamotoGroup(Ax) | [AxisSubgroup(Ax, x) : x in S]>;
  return OrbitClosure(D, Axes(Ax), S);
end function;

intrinsic ShapeGraph(Ax::Axet) -> GrphDir, GrphVertSet, GrphEdgeSet
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
    // NB we only need search in those of larger or equal size
    poss := [ j : j in [1..#verts] | #subalgs[j] le #subalgs[i]];
    
    subsets := {@ o : S in Subsets(Set(subalgs[i]), 2) | so 
              where so := exists(o){ o : o in verts[poss] | IsConjugate(G, X, o, IndexedSet(S))}@};
    subsets diff:= {@ verts[i]@};
    edges cat:= [ [ verts[i], o] : o in subsets];
  end for;
  
  return Digraph< Set(verts) | edges>;  
end intrinsic;
/*

======= Shapes =======

*/
intrinsic DominatingVertices(Gr::GrphDir) -> SetIndx
  {
  The set of vertices v in our graph that are either sources, or if there is an in edge w -> v from another vertex w there is also an edge v -> w.
  }
  return {@ v : v in Vertices(Gr) | InNeighbours(v) subset OutNeighbours(v) @};
end intrinsic;

intrinsic Sinks(Gr::GrphDir) -> SetIndx
  {
  The set of sinks of the directed graph.
  }
  return {@ v : v in Vertices(Gr) | OutDegree(v) eq 0 @};
end intrinsic;

intrinsic WeaklyConnectedComponents(Gr::GrphDir) -> SetIndx
  {
  Returns the weakly connected components of a directed graph.
  }
  UnGr := UnderlyingGraph(Gr);
  Gr_verts := Vertices(Gr);
  
  return [ sub<Gr | ChangeUniverse(comp, Gr_verts) > : comp in Components(UnGr)];
end intrinsic;

function InterpretShape(sh)
  so, exp, S := Regexp("([0-9]+)(.+)", sh);
  assert so and exp eq sh;
  return StringToInteger(S[1]), S[2];
end function;

intrinsic Shapes(Ax::Axet, FL::FusLaw) -> SetIndx
  {
  Returns the set of shapes for the axet Ax.
  }
  require HasAdmissibleTauMap(Ax, FL): "The axet does not have an admissible tau-map.";
  
  G := Group(Ax);
  X := Axes(Ax);
  Gr, Gr_v, Gr_e := ShapeGraph(Ax);
  Grvert_to_pos := func<v | Position(Vertices(Gr),v)>;
  Grvert_to_set := func<v | Support(Gr)[v@Grvert_to_pos]>;
  info := GetFusionLawInformation(FL);
  // This gives us the information about the subalgebras of the fusion law
  if not info["complete_basic_algebras"] then
    print "Warning: not all 2-generated subalgebras are known.";
  end if;
  
  basics := info["basic_algebras"];
  basics_names := IndexedSet(Keys(basics));
  nums := [ #basics[k] : k in basics_names ];
  subalgs := info["subalgebras"];
  
  comps := WeaklyConnectedComponents(Gr);
  // Sort the components by max size of subalgebra and each component by subalgebra size
  comp_dom_verts := [ Sort([ <p, SubalgebraOrb(Ax, p@Grvert_to_set)> : p in DominatingVertices(comp)], func<x,y | #y[2]-#x[2]>) : comp in comps ];
  Sort(~comp_dom_verts, func<x,y | #y[1,2] -#x[1,2]>, ~perm);
  comps := PermuteSequence(comps, perm);
  
  // We want to consider shapes up to the action of the stabiliser of the tau-map
  stab := StabiliserOfTauMap(Ax);
  
  // stab preserves domination, so it must act on the n dominating vertices
  // We will use this to dedupe the shapes
  dom_supps := [ t[1]@Grvert_to_set : t in p, p in comp_dom_verts];
  dom_supps_orbs := [ Orbit(G, X, p) : p in dom_supps];
  
  EltInOrb := function(S, x)
    assert exists(i){ i : i in [1..#S] | x in S[i]};
    return i;
  end function;
  
  D := IndexedSet([1..#dom_supps]);
  Dxstab := CartesianProduct(D, stab);
  stabact := map< Dxstab -> D | y:-> EltInOrb(dom_supps_orbs, dom_supps[y[1]]^y[2])>;
  D := GSet(stab, D, stabact);
  
  stab_act, Dstab := Action(stab, D);
  // The connected components form a partition of D
  
  // Build the action on the k components
  P := Partition(Setseq(D), [ #comp : comp in comp_dom_verts]);
  C := IndexedSet([1..#P]);
  CxDstab := CartesianProduct(C, Dstab);
  compact := map< CxDstab -> C | y:-> EltInOrb(P, P[y[1],1]^y[2])>;
  C := GSet(Dstab, C, compact);
  assert #C eq #comps;
  
  // We now take the orbits on the components and find conjugating elements
  orb_comps := Sort([ Sort(o) : o in Orbits(Dstab, C)], func<x,y|x[1]-y[1]>);
  conjs := &cat[ [ <o[1], g> where so, g := IsConjugate(Dstab, C, o[1], j) : j in o] : o in orb_comps ]; // k conjugators
  
  // Get the possibilities, one for each orbit
  // o is a subset of k components
  all_dom_verts_axets := AssociativeArray([* <v[1], Core(sub<Ax| v[1]@Grvert_to_set>)> : v in comp_dom_verts[o[1]], o in orb_comps *]);

  // For a connected component of the shape graph, GetPossibleShapes returns a set of all possible configurations of shape for the connected component.
  
  function GetPossibleShapes(i)
    // For a connected component, we consider the dominating graph and take the vertices at the top.  These define the vertices below.  Note that they may have in-edges, but only from vertices they map out to too. eg 5A.
    comp := comps[i];
    dom_verts := [ t[1] : t in comp_dom_verts[i]];
    dom_verts_axets := [ all_dom_verts_axets[v] : v in dom_verts];
    
    // We find the possible isomorphism classes of the dominating vertices and record the isomorphism
    poss := [ [ <basics_names[i], phi, psi> : i in [1..#basics] |
                 nums[i] eq #Bx and so
                      where so, phi, psi := IsIsomorphic(basics[basics_names[i]], Bx) ]
                               : Bx in dom_verts_axets];
                               
    // REMOVE vert_to_pos := func<v | Position(Vertices(comp),v)>;
    
    // Now we need to check for each combination whether their subalgebras are compatible.
    cart := CartesianProduct(poss);
    
    comp_shapes := [];
    for c in cart do
      // The ith element in c corresponds to the ith dominating vertex
      labels := [t[1] : t in c];
      
      // Now we check the neighbours of the dominating vertices (corresponding to the intersections of these subalgebras) to see that all the labels agree.

      // A dominating vertex can be an out-neightbour, so we add these
      all_labels := AssociativeArray([* <dom_verts[i], labels[i]> : i in [1..#dom_verts] *]);
      
      for i in [1..#dom_verts] do
        Ax_i := dom_verts_axets[i];
        _, phi, psi := Explode(c[i]);
      
        out := IndexedSet(OutNeighbours(dom_verts[i]));
        
        // Need to pair each subalg of the basic algebra to an element of comp and check the labels
        keys := Keys(subalgs[labels[i]]);
        for k in keys, p in subalgs[labels[i], k] do
          // the pair p@phi lies in a conjugacy class
          assert exists(w){ out[i] : i in [1..#out] |
                    IsConjugate(G, X, p@phi, out[i]@Grvert_to_set)};
          
          // Check the label is consistent if it is defined
          if w in Keys(all_labels) then
            if not all_labels[w] eq k then
              continue c; // The label is not consistent
            end if;
          else
            all_labels[w] := k;
          end if;
        end for;
      end for;

      Append(~comp_shapes, labels);
    end for;
    
    return comp_shapes;
  end function;
  
  comp_reps_poss := AssociativeArray([* <o[1], GetPossibleShapes(o[1])> : o in orb_comps*]);
  comp_poss := [ comp_reps_poss[conjs[i,1]] : i in [1..#C]];
  
  // We also need the set of axes for each one.
  // NB our ordering is based on the first in the orbit of the connected component, but the action of Dstab is based on the ordering in dom_verts
  
  // We use this for permuting indices and that acts with an inverse - CHECK!!
  dom_to_order := (Sym(#D)!Flat([ P[conjs[i,1]]^conjs[i,2] : i in [1..#comps]]))^-1;
  
  axes := [ t[2] : t in comp, comp in comp_dom_verts ];
  axes := PermuteSequence(axes, dom_to_order);
  
  cart := CartesianProduct(comp_poss);
  // We now dedupe these using the permutation action of stab on D
  
  K := Dstab;
  CP := IndexedSet([ Flat([ l : l in c]) : c in cart]);
  CPxK := CartesianProduct(CP, K);
  f := map< CPxK -> CP | y:-> PermuteSequence(y[1], y[2]^-1)>;
  // permuting indices needs an inverse to make it an action
  CP := GSet(K, CP, f);
  
  assert #CP eq #cart;
  // We pick the lexicographically best from each orbit
  // NB we could have something like 6A6A4B for several different components, so now the 4B would be out of order overall, but more usefully placed to understand.
  orb_reps := [ Sort({@ PermuteSequence(l, dom_to_order) : l in o@})[1] : o in Orbits(Dstab, CP)];
  // Now sort the set of shapes
  Sort(~orb_reps);
  
  // Should sh be a sequence?  eg for 5A it returns a single orbit, when there are two.
  return {@ Shape(Ax, FL, {@ <axes[i], r[i]> : i in [1..#D] @}) : r in orb_reps @};
end intrinsic;

intrinsic MonsterShapes(G::GrpPerm) -> SetIndx
  {
  Builds all possible faithful actions of G on unions of involutions, all tau-maps on these where the Miyamoto group is G and return all shapes on these.
  }
  all_shapes := {@@};
  Xs := InvolutionGSets(G);
  for X in Xs do
    taus := AdmissibleTauMaps(X, MonsterFusionLaw());
    for tauset in taus do
      tau, stab := Explode(tauset);
      Ax := Axet(X, tau);
      all_shapes join:= Shapes(Ax, MonsterFusionLaw());
    end for;
  end for;

  return all_shapes;
end intrinsic;

intrinsic Stabiliser(Sh::AxlShape) -> GrpPerm
  {
  The stabiliser of a given shape.
  }
  // NOT YET IMPLEMENTED
end intrinsic;





