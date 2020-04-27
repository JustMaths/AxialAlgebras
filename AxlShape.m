/*

We define a shape object

*/
declare type AxlShape: Axet;

declare attributes AxlShape:
  fusion_law,     // A FusLaw
  shape;          // Shape given as a sequence of tuples <S, type>, where S is a subset of axes and type is the type of 2-generated subgroup glued in on those axes

import AxlShape.m: MapEq, TauEq;

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
  The shape of Sh.
  }
  return Sh`axes;
end intrinsic;

intrinsic Hash(Sh::AxlShape) -> RngIntElt
  {
  The hash value of a shape.
  }
  return Hash(<FusionLaw(Sh), Group(Sh), Axes(Sh), Tau(Sh), Shape(Sh)>);
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











