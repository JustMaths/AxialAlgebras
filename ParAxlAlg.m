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



intrinsic Print(A::ParAxlAlg)
  {
  Prints a partial axial algebra.
  }
  
end intrinsic;

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

intrinsic Hash(A::ParAxlAlg) -> RngIntElt
  {
  }
  return Hash(Module(M));  
end intrinsic;

intrinsic 'eq'(A::ParAxlAlg, B::ParAxlAlg) -> BoolElt
  {}
  // Not yet implemented.
end intrinsic;


