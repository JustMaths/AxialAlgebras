/*

We define a shape object and implement some basic functions like equality

** Fix this for working with arbitrary fusion law etc

*/
declare type Axet;

declare attributes Axet:
  fusion_law,     // A FusLaw
  axes,           // A GSet of the axes
  tau,            // A map from Ax \times T to the group, where $T$ is the set of linear characters of the grading group of the fusion law
  Miyamoto_group; // The Miyamoto group on the axes

declare type AxlShape: DecAlg;

declare attributes AxlShape:
  shape,          // Shape given as a sequence of tuples <S, type>, where S is a subset of axes and type is the type of 2-generated subgroup glued in on those axes

intrinsic Information(Ax::Axet) -> List
  {
  Returns the information for printing.
  }
  return [* GroupName(MiyamotoGroup(Ax)), Join([ IntegerToString(#o) : o in Orbits(MiyamotoGroup(Ax), Axes(Ax))], "+") *];
end intrinsic;

intrinsic Information(Sh::AxShape) -> List
  {
  Returns the information for printing.
  }
  return [* GroupName(MiyamotoGroup(Sh)), Join([ IntegerToString(#o) : o in Orbits(MiyamotoGroup(Sh), Axes(Sh))], "+"), &cat[ t[2] : t in Shape(Sh)]; *];
end intrinsic;

intrinsic Print(Ax::Axet)
  {
  Prints an axet.
  }
  info := Information(Ax);
  printf "Axet for the group %o, on %o axes", info[1], info[2];
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
intrinsic FusionLaw(Ax::Axet) -> FusLaw
  {
  The fusion law of an axet.
  }
  return Ax`fusion_law;
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

intrinsic Shape(Sh::AxlShape) -> SeqEnum
  {
  The shape of Sh.
  }
  return Sh`axes;
end intrinsic;

intrinsic Group(Ax::Axet) -> GrpPerm
  {
  The full group of an axet.
  }
  return Group(Axes(Ax));
end intrinsic;

intrinsic MiyamotoGroup(Ax::Axet) -> GrpPerm
  {
  The Miyamoto group of an axet.
  }
  if not assigned Ax`Miyamoto_group then
    Ax`Miyamoto_group := sub<Group(Ax) | Image(Tau(Ax))>;
  end if;
  return Ax`Miyamoto_group;
end intrinsic;

intrinsic Hash(Ax::Axet) -> RngIntElt
  {
  The hash value of an axet.
  }
  return Hash(<FusionLaw(Ax), Group(Ax), Axes(Ax), Tau(Ax)>);
end intrinsic;

intrinsic Hash(Sh::AxlShape) -> RngIntElt
  {
  The hash value of a shape.
  }
  return Hash(<FusionLaw(Ax), Group(Sh), Axes(Sh), Tau(Sh), Shape(Sh)>);
end intrinsic;
/* 

===========  Creation of axets and shapes  ===========

*/
intrinsic Axet(Ax::GSet, tau::Map, FL::FusLaw) -> Axet
  {
  Builds the an axet.
  }
  require IsTauMap(Ax, FL, tau): "You have not given a valid tau-map.";
  
  Ax := New(Axet);
  Ax`fusion_law := FL;
  Ax`axes := Ax;
  Ax`tau := tau;
  
  return Ax;
end intrinsic;

intrinsic Axet(Sh::AxlShape) -> Axet
  {
  The underlying axet for a shape.
  }
  Ax := New(Axet);
  Ax`fusion_law := FusionLaw(Sh);
  Ax`axes := Axes(Sh);
  Ax`tau := Tau(Sh);
  
  return Ax;
end intrinsic;

intrinsic Shape(Ax::Axet, shape::SeqEnum) -> AxlShape
  {
  Builds the shape of an axet.  NB no attempt is made to check the validity of the labels of the edges in the shape.
  }
  require forall{ t : t in shape | t[1] subset Axes(Ax) and Type(t[2]) eq MonStgElt }: "You have not given a valid shape.";
  
  Sh := New(AxlShape);
  Sh`fusion_law := FusionLaw(Ax);
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

intrinsic Shape(Ax::GSet, tau::Map, shape::SeqEnum, FL::FusLaw) -> AxlShape
  {
  Builds the shape object.
  }
  require IsTauMap(Ax, FL, tau): "You have not given a valid tau-map.";
  require forall{ t : t in shape | t[1] subset Ax and Type(t[2]) eq MonStgElt }: "You have not given a valid shape.";

  Sh := New(AxlShape);
  Sh`fusion_law := FL;  
  Sh`axes := Ax;
  Sh`tau := tau;
  Sh`shape := shape;
  
  return Sh;
end intrinsic;
/*

======= Equality and isomorphism =======

*/
function GSetEq(Ax1, Ax2)
  return Ax1 eq Ax2 and ActionImage(Group(Ax1), Ax1) eq ActionImage(Group(Ax2), Ax2);
end function;

function MapEq(f, g)
  return Domain(f) eq Domain(g) and [ i@f : i in Domain(f)] eq [ i@g : i in Domain(g)];
end function;

intrinsic 'eq'(S::Axet, T::Axet) -> BoolElt
  {
  Equality of axets.
  }
  return FusionLaw(S) eq FusionLaw(T) and GSetEq(Axes(S), Axes(T)) and MapEq(Tau(S), Tau(T));
end intrinsic;

intrinsic 'eq'(S::AxlShape, T::AxlShape) -> BoolElt
  {
  Equality of shapes.
  }
  return FusionLaw(S) eq FusionLaw(T) and GSetEq(Axes(S), Axes(T)) and MapEq(Tau(S), Tau(T)) and Shape(S) eq Shape(T);
end intrinsic;

intrinsic IsIsomorphic(S::Axet, T::Axet) -> BoolElt, GrpPermElt, Map
  {
  Tests if S and T are isomorphic.  If so, it returns a pair, perm in Sym(|S|) and homg:Miy1->Miy2 such that
  
  (i^g)^perm = (i^perm)^(g@homg) for all g in G1.
  
  i:->  i^(perm)^-1 @tau2^perm = tau2
  }
  // Not yet implemented
end intrinsic;

intrinsic IsIsomorphic(Sh1::AxlShape, Sh2::AxlShape) -> BoolElt, GrpPermElt, Map
  {
  Tests if Sh1 and Sh2 are isomorphic.  If so, it returns a pair, perm in Sym(|Ax1|) and homg:Miy1->Miy2 such that
  
  (i^g)^perm = (i^perm)^(g@homg) for all g in G1.
  
  i:->  i^(perm)^-1 @tau2^perm = tau2
  }
  // Not yet implemented
end intrinsic;
/*

======= Tau maps =======

*/
intrinsic TauAction(Ax::Axet) -> GSet
  {
  
  }
  // Not yet implemented
end intrinsic;

intrinsic TauMaps(Ax::GSet) -> SeqEnum
  {
  Given a GSet Ax, we find all the admissible tau maps up to automorphisms of the action.
  }
  // Not yet implemented
end intrinsic;

IsTauMap(Ax::GSet, FL::FusLaw, tau::Map) -> BoolElt
  {
  Checks whether tau is a valid tau-map.
  }
  
  // Not yet implemented
end intrinsic;

/*
function WellDefined(S)
  if assigned S`shape then
    return assigned S`axes and assigned S`tau;
  elif 
    assigned S`tau then
    return assigned S`axes;
  end if;
  return assigned S`axes;
end function;

intrinsic 'subset'(S::AxlShape, T::AxlShape) -> BoolElt
  {
  Is S a shape of type T?
  }
  if assigned S`shape then
    require WellDefined(S): "S isn't a properly assigned shape.";
    if assigned T`shape then
      require WellDefined(T): "T isn't a properly assigned shape.";
      return S eq T;
    else
      return false;
    end if;
  elif assigned S`tau then
    require WellDefined(S): "S isn't a properly assigned shape.";
    if assigned T`tau then
      require WellDefined(T): "T isn't a properly assigned shape.";
      return GSetEq(S`axes, T`axes) and MapEq(S`tau, T`tau);
    else
      return false;
    end if;
  elif assigned S`axes then
    if assigned T`axes then
      require WellDefined(T): "T isn't a properly assigned shape.";
      return GSetEq(S`axes, T`axes);
    else
      return false;
    end if;
  end if;
  return true; // This is the empty shape
end intrinsic;
*/

intrinsic IsIsomorphicActionAndTauMap(Sh1::AxlShape, Sh2::AxlShape) -> BoolElt, GrpPermElt, Map
  {
  Tests if Sh1 and Sh2 are isomorphic.  If so, it returns a pair, perm in Sym(|Ax1|) and homg:Miy1->Miy2 such that
  
  (i^g)^perm = (i^perm)^(g@homg) for all g in G1.
  
  i:->  i^(perm)^-1 @tau2^perm = tau2
  }
  Ax1, tau1 := ExplodeShape(Sh1);
  Ax2, tau2 := ExplodeShape(Sh2);
  require assigned Ax1 and assigned tau1 and assigned Ax2 and assigned tau2: "The shapes aren't fully assigned.";
  Miy1 := Sh1`Miyamoto_group;
  Miy2 := Sh2`Miyamoto_group;
  
  if #Ax1 ne #Ax2 or Order(Miy1) ne Order(Miy2) then
    return false, _, _;
  end if;
  
  // Find the equivalence between the GSets
  act1, GG1 := Action(Miy1, Ax1);
  act2, GG2 := Action(Miy2, Ax2);
  so, perm := IsConjugate(Sym(#Ax1), GG1, GG2);
  if not so then
    return false, _, _;
  end if;
  homg := hom<Miy1 -> Miy2 | [<g,((g@act1)^perm)@@act2> : g in Generators(Miy1) join {Miy1!1}]>;
  assert2 forall{<i,g> : i in Ax1, g in Generators(Miy1) | Image(g,Ax1,i)^perm eq Image(g@homg, Ax2, i^perm)};
  
  // We form the tau map for the conjugated Ax1
  tau_adj := map<Ax2 -> Group(Ax2) | i:->(i^(perm^-1))@tau1@homg>;
  
  // Find the equivalence between the tau maps
  GAx2 := Stabiliser(Sym(#Ax2), Set(Orbits(Miy2, Ax2)));
  N := Normaliser(GAx2, GG2);

  // We must define equality of maps
  orb_reps := {@ o[1] : o in Orbits(Miy2, Ax2)@};
  MapEq := function(f,g)
    return forall{i: i in orb_reps | i@f eq i@g};
  end function;
    
  // The action on tau maps is
  // tau_n := tau(i^(n^-1))^n
  
  so := exists(n){n : n in N | MapEq(tau2, map<Ax2 -> Group(Ax2) |
                        i:-> (((i^(n^-1))@tau_adj@act2)^n)@@act2>)};
  
  if not so then
    return false, _, _;
  end if;
  
  perm := perm*n;
  homg := hom<Miy1 -> Miy2 | [<g,((g@act1)^perm)@@act2> : g in Generators(Miy1) join {Miy1!1}]>;
  assert2 MapEq(tau2, map<Ax2 -> Group(Ax2) | i:->(i^(perm^-1))@tau1@homg>);
  
  return true, perm, homg;
end intrinsic;

intrinsic IsIsomorphic(S::AxlShape, T::AxlShape) -> BoolElt, Map
  {
  Checks whether S and T are isomorphic shapes and if so also returns an isomorphism of axes as GSets.
  }
  // Not yet implemented
end intrinsic;

intrinsic RestrictShape(Sh::AxlShape, axes::SetIndx : K := sub<Sh`group | [i@Sh`tau : i in axes]>) -> SeqEnum, SeqEnum
  {
  Given a shape Sh, and a set of axes acted upon by K, calculate the restriction of the shape to the set of axes.  Returns the type and the sequence of types seen from the original shape.
  }
  return RestrictShape(Sh`axes, Sh`tau, Sh`shape, axes: K:=K);
end intrinsic;

intrinsic ExplodeShape(Sh::AxlShape) -> GSet, Map, SeqEnum
  {
  Returns the axes, tau-map and shape.
  }
  attrs := ["axes", "tau", "shape"];
  
  for i in [3..1 by -1] do
    if assigned Sh``(attrs[i]) then
      return Explode([* Sh``(attrs[j]) : j in [1..i]*]);
    end if;
  end for;
end intrinsic;

