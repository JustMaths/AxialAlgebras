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
intrinsic Sources(Gr::GrphDir) -> IndxSet
  {
  The set of sources of the directed graph.
  }
  return {@ v : v in Vertices(Gr) | InDegree(v) eq 0 @};
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
  
  orbs := [ sub<Ax| p> : p in Support(Gr)];
  comps := WeaklyConnectedComponents(Gr);
  all_sources := AssociativeArray([* <comp, Sources(comp)> : comp in comps*]);
  
  // For a connected component of the shape graph, GetPossibleShapes returns a set of all possible configurations of shape for the connected component.
  function GetPossibleShapes(comp)
    vert_to_pos := func<v | Position(Vertices(comp),v)>;
    
    // For a connected component, the vertices with only out arrows are the ones which dominate.  These define the vertices below.
    sources := all_sources[comp];
    sources_axets := [ orbs[v@Grvert_to_pos] : v in sources];
    poss := [ [ basics_names[i] : i in [1..#basics] | nums[i] eq #Bx] : Bx in sources_axets];
    
    // Now we need to check for each combination whether their subalgebras are compatible.
    cart := CartesianProduct(poss);
    
    comp_shapes := [];
    for c in cart do
      labels := [];
      // Set the labels
      for i in [1..#sources] do
        labels[sources[i]@vert_to_pos] := c[i];
      end for;
      
      // Now recursively cascade the labels down the graph, checking for compatibility at each stage
      queue := sources;
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
        queue join:=out;
      end while;
      assert IsComplete(labels);
      // The labels are all defined and consistent
      Append(~comp_shapes, labels);
    end for;
    
    return comp_shapes;
  end function;

  // We may now build all the possible shapes
  cart := [ GetPossibleShapes(comp) : comp in comps ];
  //sources := [ [ Position(Vertices(comp), v) : v in Sources(comp)] : comp in comps];
  shapes := [];
  for c in cart do
    sh := [* < Set(Axes(orbs[w@Grvert_to_pos])), c[Position(Vertices(comps[i]), w)]>
                     : w in all_sources[comps[i]], i in [1..#c] *];
    Append(~shapes, AxlShape(Ax, sh));
  end for;
  
  return IndexedSet(shapes);
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





