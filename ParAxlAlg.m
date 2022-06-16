/*

Code to create partial axial algebras

   version 2

*/

// Set this to the relative directory of where the library is
library_location := "../AxialAlgebras/library";

declare type ParAxlAlg[ParAxlAlgElt];

declare attributes ParAxlAlg:
  fusion_law,     // A FusLaw for the fusion law
  shape,          // An AxlShape giving the shape
  axes_map,       // A map from the AxlShape to the axes
  group,          // The automorphism group G on the axes
  Miyamoto_group, // The Miyamoto group G_0
  W,              // A GModDec for the partial algebra as a G-module
  V,              // A GModDec for the submodule of W where we can multiply
  mult,           // A bilinear map giving the multilpication on V
  subalgs,        // A SubAlg
  axes,           // A SeqEnum of AxlAxis which are the axes
  rels;           // A GModDec of relations

declare attributes ParAxlAlgElt:
  parent,         // parent
  elt;            // element

declare type SubAlg;

declare attributes SubAlg:
  subsps,         // A List of ???
  maps,           // A List of tups < map, homg, j>, where map: subsps -> algs[j]`W is a hom
                  // and homg: Group(A) -> Group(alg) is a group hom
  algs;           // A SetIndx of algebras

declare type AxlAxis;

declare attributes AxlAxis:
  axis,           // ParAxlAlgElt which is the idempotent
  adjoint,        // The adjoint action as a map from W to W
  stabiliser,     // A GrpPerm which is the stabiliser H of the axis
  module,         // A GModDec which is W as an H-module
  lift,           // A lift map from W as an H-module to W as a G-module
  restrict,       // A restriction map from W as an G-module to W as a H-module
  fusion_law,     // A FusLaw for the fusion law
  pure_subsets;   // Assoc of submodules indexed by subsets of the pure 


// --------------------------------------------
//
//             ParAxlAlg functions
//
// --------------------------------------------
intrinsic Print(A::ParAxlAlg)
  {
  Prints a partial axial algebra.
  }
  
end intrinsic;
/*

======= Invariants of an axial algebra =======

*/
intrinsic AxetShape(A::ParAxlAlg) -> AxlShape
  {
  Returns the shape of an algebra.
  }
  return A`shape;
end intrinsic;

intrinsic Dimension(A::ParAxlAlg) -> RngIntElt
  {
  Dimension of the partial algebra.
  }
  return Dimension(A`Wmod);
end intrinsic;

intrinsic BaseRing(A::ParAxlAlg) -> Rng
  {
  Base field of the partial algebra.
  }
  return BaseRing(A`Wmod);
end intrinsic;

intrinsic BaseField(A::ParAxlAlg) -> Rng
  {
  "
  }
  return BaseRing(A);
end intrinsic;

intrinsic GModule(A::ParAxlAlg) -> GrpPerm
  {
  The algebra as a module.
  }
  return A`Wmod;
end intrinsic;

intrinsic Group(A::ParAxlAlg) -> GrpPerm
  {
  Group of the partial algebra.
  }
  return Group(A);
end intrinsic;

intrinsic MiyamotoGroup(A::ParAxlAlg) -> GrpPerm
  {
  Miyamoto group of the partial algebra.
  }
  return A`Miyamoto_group;
end intrinsic;

intrinsic FusionLaw(A::ParAxlAlg) -> FusLaw
  {
  The fusion law.
  }
  return A`fusion_law;
end intrinsic;

intrinsic Axes(A::ParAxlAlg) -> SetIndx
  {
  The axes.
  }
  return Axes(Shape(A))@A`axes_map;
end intrinsic;
/*

======= Functions on a subalgebra =======

*/
intrinsic Hash(A::ParAxlAlg) -> RngIntElt
  {
  }
  return Hash(Module(M));  
end intrinsic;

intrinsic 'eq'(A::ParAxlAlg, B::ParAxlAlg) -> BoolElt
  {}
  // Not yet implemented.
end intrinsic;
/*

======= Creating specific elements =======

*/
intrinsic Zero(A::ParAxlAlg) -> ParAxlAlgElt
  {
  Creates the zero element of A.
  }
  return CreateElement(A, Zero(GModule(A)));
end intrinsic;

intrinsic Basis(A::ParAxlAlg) -> SeqEnum
  {
  Basis of the partial algebra.
  }
  return [ CreateElement(A, v) : v in Basis(GModule(A))];
end intrinsic;

intrinsic '.'(A::ParAxlAlg, i::RngIntElt) -> ParAxlAlgElt
  {
  The ith basis element of the partial algebra.
  }
  bas := Basis(A);
  require i gt 0 and i le #bas: "Argument 2 (", i, ") should be in the range", [1..#bas];
  return Basis(A)[i];
end intrinsic;
// --------------------------------------------
//
//             ParAxlAlgElt functions
//
// --------------------------------------------
/*

======= ParAxlAlgElt functions and operations =======

*/
intrinsic Parent(x::ParAxlAlgElt) -> ParAxlAlg
  {
  Return the parent of x.
  }
  return x`parent;
end intrinsic;

intrinsic Element(x::ParAxlAlgElt) -> .
  {
  Returns x as an element of the GModule.
  }
  return x`elt;
end intrinsic;

intrinsic Eltseq(x::ParAxlAlgElt) -> SeqEnum
  {
  Returns the elements of x as a sequence.
  }
  return Eltseq(Element(x));
end intrinsic;

intrinsic Print(x::ParAxlAlgElt)
  {
    Prints x.
  }
  printf "%o", x`elt;
end intrinsic;

intrinsic Hash(x::ParAxlAlgElt) -> RngIntElt
  {
    Returns the hash value for x.
  }
  return Hash(Eltseq(x));
end intrinsic;

// I had this as an intrinsic before, but maybe a function is better??
function CreateElement(A, x)
  xx := New(ParAxlAlgElt);
  xx`parent := A;
  xx`elt := GModule(A)!x;
  
  return xx;
end function;

intrinsic IsCoercible(A::ParAxlAlg, x::.) -> BoolElt, .
  {
  Returns whether x is coercible into A and the result if so.
  }
  if Type(x) eq RngIntElt and x eq 0 then
    return true, Zero(A);
  elif ISA(Type(x), ParAxlAlgElt) and x`parent eq A then
    return true, x;
  elif so where so, xx := IsCoercible(GModule(A), x) then
    return true, CreateElement(A, x);
  // More to add here!!
  end if;
  return false, "Illegal coercion.";
end intrinsic;
/*

======= Operations on the elements =======

*/
intrinsic '-'(x::ParAxlAlgElt) -> ParAxlAlgElt
  {
    Returns the negation of x.
  }
  return CreateElement(Parent(x), -Element(x));
end intrinsic;

intrinsic '+'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> ParAxlAlgElt
  {
    Returns the sum of x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same partial axial algebra.";
  return CreateElement(Parent(x), Element(x)+Element(y));
end intrinsic;

intrinsic '-'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> ParAxlAlgElt
  {
    Returns the difference of x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same partial axial algebra.";
  return CreateElement(Parent(x), Element(x)-Element(y));
end intrinsic;

intrinsic '*'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> ParAxlAlgElt
  {
    Returns the product of x and y.
  }
  // Not yet implemented!!
end intrinsic;

intrinsic '*'(r::RngElt, x::ParAxlAlgElt) -> ParAxlAlgElt
  {
    Returns the scalar product of r and x.
  }
  require r in BaseRing(Parent(x)): "The scalar given is not in the base ring of the algebra.";
  return CreateElement(Parent(x), r*Element(x));
end intrinsic;

intrinsic '*'(x::ParAxlAlgElt, r::RngElt) -> ParAxlAlgElt
  {
  "
  }
  return r*x;
end intrinsic;

intrinsic '/'(x::ParAxlAlgElt, r::RngElt) -> ParAxlAlgElt
  {
    Returns the scalar division of x by r.
  }
  R := BaseRing(Parent(x));
  require r in R: "The scalar given is not in the base ring of the algebra.";
  so, rinv := IsInvertible(R!r);
  require so: "The scalar is not invertible.";
  return CreateElement(Parent(x), rinv*Element(x));
end intrinsic;
 
intrinsic '*'(x::ParAxlAlgElt, g::GrpElt) -> ParAxlAlgElt
  {
    Returns the image of x under the action of g.
  }
  A := Parent(x);
  if Parent(g) eq Group(A) then
    return A!(Element(x)*g);
  end if;
  error "%o is not in the group.";
end intrinsic;
/*

======= Comparisons and Membership for the elements =======

*/
intrinsic 'eq'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> BoolElt
  {
    Returns whether x equals y.
  }
  require Parent(x) eq Parent(y): "The two elements are not in the same partial axial algebra.";
  return Element(x) eq Element(y);
end intrinsic;

intrinsic 'in'(x::ParAxlAlgElt, A::ParAxlAlg) -> BoolElt
  {
    Returns whether x is in A.
  }
  return Parent(x) eq A;
end intrinsic;

// NB, we get ne and notin for free
/*

======= Predicates for the elements =======

*/
intrinsic IsZero(x::ParAxlAlgElt) -> BoolElt
  {
    Returns whether x is the zero element.
  }
  return IsZero(x`elt);
end intrinsic;
// --------------------------------------------
//
//             AxlAxis functions
//
// --------------------------------------------
/*

======= Dec functions and operations =======

"*/
intrinsic Print(D::AxlAxis)
  {
  Prints a Axial decomposition.
  }
  printf "Decomposition of a %o-dimensional axial algebra into %o parts: %o", 
    Dimension(Parent(D)), NumberOfParts(D), 
    [ Dimension(Part(D,i)) : i in Elements(FusionLaw(D)) ];
end intrinsic;

intrinsic Axis(D::AxlAxis) -> .
  {
    Returns the axis for D.
  }
  return D`axis;
end intrinsic;

intrinsic FusionLaw(D::AxlAxis) -> FusLaw
  {
    Returns the fusion law for D.
  }
  return D`fusion_law;
end intrinsic;

intrinsic Evaluation(D::AxlAxis) -> Map
  {
    Returns the evaluation for D.
  }
  return Evaluation(FusionLaw(D));
end intrinsic;

intrinsic Hash(D::AxlAxis) -> RngIntElt
  {
  Returns the hash value for D.
  }
  return Hash(D`parts);
end intrinsic;

intrinsic 'eq'(D1::AxlAxis, D2::AxlAxis) -> BoolElt
  {
  Returns whether D1 equals D2.
  }
  return D1`parts eq D2`parts and Axis(D1) eq Axis(D2);
end intrinsic;

intrinsic Parent(D::AxlAxis) -> .
  {
  Returns the algebra for which D is a decomposition.
  }
  return D`parent;
end intrinsic;

// Can we implement the following using [] notation
intrinsic Part(D::AxlAxis, x::FusLawElt) -> ModTupRng
  {
  Returns the part of D for the fusion law element x.
  }
  require x in Elements(FusionLaw(D)): "The element is not in the fusion law.";
  return D`parts[x];
end intrinsic;

intrinsic Part(D::AxlAxis, X::SetIndx[FusLawElt]) -> ModTupRng
  {
  Return the sum of parts of D for the fusion law elements in X.
  }
  return &+[ Part(D,x) : x in X ];
end intrinsic;

intrinsic NumberOfParts(D::AxlAxis) -> RngIntElt
  {
  Returns the number of parts in decomposition D.
  }
  return #D`parts;
end intrinsic;

intrinsic Nparts(D::AxlAxis) -> RngIntElt
  {
  "
  }
  return NumberOfParts(D);
end intrinsic;



