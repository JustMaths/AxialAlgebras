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
intrinsic DominatingVertices(Gr::GrphDir) -> IndxSet
  {
  The set of vertices v in our graph that are either sources, or if there is an in edge w -> v from another vertex w there is also an edge v -> w.
  }
  return {@ v : v in Vertices(Gr) | InNeighbours(v) subset OutNeighbours(v) @};
end intrinsic;

intrinsic Sinks(Gr::GrphDir) -> IndxSet
  {
  The set of sinks of the directed graph.
  }
  return {@ v : v in Vertices(Gr) | OutDegree(v) eq 0 @};
end intrinsic;

intrinsic WeaklyConnectedComponents(Gr::GrphDir) -> IndxSet
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

intrinsic Shapes(Ax::Axet, FL::FusLaw) -> IndxSet
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
  
  // For a connected component of the shape graph, GetPossibleShapes returns a set of all possible configurations of shape for the connected component.
  
  forward all_dom_verts_axets;
  
  // EDIT the following to correct dom_verts, all_dom_verts etc to the right thing
  function GetPossibleShapes(i)
    // For a connected component, we consider the dominating graph and take the vertices at the top.  These define the vertices below.  Note that they may have in-edges, but only from vertices they map out to too. eg 5A.
    comp := comps[i];
    dom_verts := comp_dom_verts[i];
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
  
  // We want to consider shapes up to the action of the stabiliser of the tau-map
  stab := StabiliserOfTauMap(Ax);
  
  // stab preserves domination, so it must act on the dominating vertices
  // We will use this to dedupe the shapes
  dom_supps := [ t[1]@Grvert_to_set : t in p, p in comp_dom_verts];
  dom_supps_orbs := [ Orbit(G, X, p) : p in dom_supps];
  
  EltInOrb := function(x)
    assert exists(i){ i : i in [1..#dom_supps] | x in dom_supps_orbs[i]};
    return i;
  end function;
  
  D := IndexedSet([1..#dom_supps]);
  Dxstab := CartesianProduct(D, stab);
  // Only need to check one element from the connected component
  stabact := map< Dxstab -> D | y:-> EltInOrb(dom_supps[y[1]]^y[2])>;
  D := GSet(stab, D, stabact);
  
  
  
  
  /*
  
  
  
  
  
  // stab preserves domination, so it must permute the connected components of Gr
  // Build the action on the index of connected components
  
  comp_supps := [ Support(comp) : comp in comps];
  comp_supps_orbs := [ &join{@ Orbit(G, X, p) : p in S @} : S in comp_supps];
  
  EltInOrb := function(x)
    assert exists(i){ i : i in [1..#comps] | x in comp_supps_orbs[i]};
    return i;
  end function;
  
  num_comps := IndexedSet([1..#comps]);
  numxstab := CartesianProduct(num_comps, stab);
  // Only need to check one element from the connected component
  stabact := map< numxstab -> num_comps | y:-> EltInOrb(comp_supps[y[1],1]^y[2])>;
  num_comps := GSet(stab, num_comps, stabact);

  // We may now build all the possible shapes
  
  num_comps_orbs := Orbits(stab, num_comps);
  all_dom_verts := AssociativeArray([* <comps[o[1]], DominatingVertices(comps[o[1]])> : o in num_comps_orbs*]);
  all_dom_verts_axets := AssociativeArray([* <v, Core(sub<Ax| v@Grvert_to_set>)> : v in all_dom_verts[k], k in Keys(all_dom_verts)*]);
  
  // Get the possibilities, one for each orbit
  comp_reps_poss := [ GetPossibleShapes(comps[o[1]]) : o in num_comps_orbs];
  comp_poss := [ comp_reps_poss[j] where so := exists(j){ j : j in [1..#num_comps_orbs] | i in num_comps_orbs[j]} : i in [1..#comps]];
  
  cart := CartesianProduct(comp_poss);
  // We now dedupe these using the permutation action of stab
  
  K := ActionImage(stab, num_comps);
  C := IndexedSet([ [ l : l in c] : c in cart]);
  CxK := CartesianProduct(C, K);
  permstab := map< CxK -> C | y:-> PermuteSequence(y[1], y[2])>;
  C := GSet(K, C, permstab);
  
  assert #C eq #cart;
  orbs := Orbits(K, C);
  // We pick the lexicographically best from each orbit
  // NB we could have something like 6A6A4B for several different components, so now the 4B would be out of order overall, but more usefully placed to understand.
  
  
  
  
  
  shapes := [];
  for c in cart do
    // Should sh be a sequence?  eg for 5A it returns a single orbit, when there are two.
    sh := {@ < IndexedSet(Axes(orbs[w@Grvert_to_pos])), c[i, Position(Vertices(comps[i]), w)]>
                     : w in all_dom_verts[comps[i]], i in [1..#c] @};
    Append(~shapes, Shape(Ax, FL, sh));
  end for;
  
  // Here we need to dedupe by the action of the group
  
  
  shapes := IndexedSet(shapes);
  
  // Sort by size too
  
  
  
  
  // Sort lexicographically by shape
  Sort(~shapes, func<x,y| Information(y)[3] lt Information(x)[3] select 1 else Information(y)[3] gt Information(x)[3] select -1 else 0>);
  return shapes;


      
      
      queue := dom_verts;
      while not IsEmpty(queue) do
        v := queue[1];
        queue := queue[2..#queue];

        Ax_v := orbs[v@Grvert_to_pos];
        label_v:= labels[v@vert_to_pos];
        so, phi, psi := IsIsomorphic(basics[label_v], Core(Ax_v));
        if not so then
          continue c;
        end if;

        num_v := InterpretShape(label_v);
        out := IndexedSet(OutNeighbours(v));
        out_algs := [ orbs[w@Grvert_to_pos] : w in out];
        
        // They are isomorphic as axets, so we now try to pair up the subalgebras of the putative basic algebra with that of Ax_v
        keys := Keys(subalgs[label_v]);
        
        for k in keys do
          num_k := InterpretShape(k);
          for p in subalgs[label_v, k] do
            // the pair p lies in a conjugacy class
            assert exists(w){ out[i] : i in [1..#out] | #out_algs[i] eq num_k and
                      IsConjugate(G, X, p@phi, out[i]@Grvert_to_set)};
            
            // Check the label is consistent if it is defined
            if IsDefined(labels, w@vert_to_pos) then
              if not labels[w@vert_to_pos] eq k then
                continue c;
              end if;
            else
              labels[w@vert_to_pos] := k;
            end if;
          end for;
        end for;
        
        // all the labels for the out vertices (subalgebras) should now be defined
        assert forall{ w : w in out | IsDefined(labels, w@vert_to_pos)};
        // Add the out edges to the queue
        Include(~completed, v);
        queue join:=out diff completed;
      end while;
      assert IsComplete(labels);
      // The labels are all defined and consistent
      Append(~comp_shapes, labels);
    end for;
    
    return comp_shapes;
  end function;
  
  
  
  
  
  
  
  
  // NB we don't actually use all of these, other than to sort
  orbs := [ sub<Ax| p> : p in Support(Gr)];
  
  // We sort, so that shapes are more comparable.  Sort so that the components with the largest max axet are first
  function MaxAxetSize(S)
    return Max([ #orbs[p@Grvert_to_pos] : p in S]);
  end function;
  Sort(~comps, func<x,y| MaxAxetSize(Vertices(y)) - MaxAxetSize(Vertices(x))>);
  
  // We could only compute this as we go along (and so only do one per orbit of connected component under the action of the stabiliser of tau) if this is expensive
  // all_dom_verts := AssociativeArray([* <comp, DominatingVertices(comp)> : comp in comps*]);
  
  
  
    
  
  
  
  // We may now build all the possible shapes
  cart := CartesianProduct([ GetPossibleShapes(comp) : comp in comps ]);
  shapes := [];
  for c in cart do
    // Should sh be a sequence?  eg for 5A it returns a single orbit, when there are two.
    sh := {@ < IndexedSet(Axes(orbs[w@Grvert_to_pos])), c[i, Position(Vertices(comps[i]), w)]>
                     : w in all_dom_verts[comps[i]], i in [1..#c] @};
    Append(~shapes, Shape(Ax, FL, sh));
  end for;
  
  // Here we need to dedupe by the action of the group
  
  
  shapes := IndexedSet(shapes);
  
  // Sort by size too
  
  
  
  
  // Sort lexicographically by shape
  Sort(~shapes, func<x,y| Information(y)[3] lt Information(x)[3] select 1 else Information(y)[3] gt Information(x)[3] select -1 else 0>);
  return shapes;
  */
end intrinsic;

intrinsic MonsterShapes(G::GrpPerm) -> IndxSet
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





