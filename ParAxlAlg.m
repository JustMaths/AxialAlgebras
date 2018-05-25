/*

We define a new class of object called a partial axial algebra, together with some functions for it to work.

*/

// Set this to the relative directory of where the library is
library_location := "library";

declare type ParAxlAlg[ParAxlAlgElt];

declare attributes ParAxlAlg:
  W,              // A vectorspace on which partial multiplication can be defined
  Wmod,           // A G-module representing the same vector space
  V,              // A vectorspace on which we know how to multiply
  mult,           // SeqEnum Multiplication table for V whose entries are ModTupFldElts
  shape,          // A SetIndx of tuples < S, type> where S is a SetIndx of all axes in the
                  // subalgebra of shape type.
  number_of_axes, // The number of axes, which are always the last basis elements of W
  fusion_table,   // A FusTab which is the fusion table
  subalgs,        // A SubAlg
  axes,           // A SeqEnum of AxlAxis which are the axes
  rels;           // A SetIndx of relations which are elements of W

declare attributes ParAxlAlgElt:
  parent,         // parent
  elt;            // element

declare type SubAlg;

declare attributes SubAlg:
  subsps,         // A SetIndx of vector (sub)spaces
  maps,           // A List of tups < map, homg, j>, where map: subsps -> algs[j]`W is a hom
                  // and homg: Group(alg) -> Group(A) is a group hom
  algs;           // A SetIndx of partial algebras

declare type AxlAxis;

declare attributes AxlAxis:
  id,             // ParAxlAlgElt which is the idempotent
  stab,           // A GrpPerm which is the stabiliser of the axis
  inv,            // A GrpPermElt which is the Miyamoto involution in stab
  WH,             // ModGrp W as a H-module where H=stab
  even,           // Assoc of sums of even eigenspaces
  odd;            // Assoc of odd eigenspace

// id should be a ParAxlAlgElt...

/*

Programming note to self:

you can just coerce to move between vector spaces and G-modules

*/
declare verbose ParAxlAlg, 4;

intrinsic 'eq'(A::Assoc, B::Assoc) -> BoolElt
  {
  Equality for AssociativeArrays.
  }
  return (Universe(A) cmpeq Universe(B)) and (Keys(A) eq Keys(B)) and forall{ k : k in Keys(A) | A[k] cmpeq B[k] };
end intrinsic;

/*

intrinsics for partial axial algebras

*/
intrinsic Print(A::ParAxlAlg)
  {
  Prints a partial axial algebra.
  }
  if assigned A`W and assigned A`V and assigned A`axes and assigned A`shape and assigned A`number_of_axes then
    printf "Partial axial algebra of shape %o, dimension %o, with known multiplication of dimension %o and %o axes in %o class%o", &cat [sh[2] : sh in A`shape], Dimension(A`W), Dimension(A`V), A`number_of_axes, #A`axes, #A`axes eq 1 select "" else "es";
  elif assigned A`W and assigned A`V and assigned A`shape and assigned A`number_of_axes then
    printf "Partial axial algebra of shape %o, dimension %o, with known multiplication of dimension %o and %o axes", &cat [sh[2] : sh in A`shape], Dimension(A`W), Dimension(A`V), A`number_of_axes;
  elif assigned A`W and assigned A`V then
    printf "Partial axial algebra of dimension %o, with known multiplication of dimension %o", Dimension(A`W), Dimension(A`V);
  elif assigned A`W then
    printf "Partial axial algebra of dimension %o", Dimension(A`W);
  end if;
end intrinsic;

intrinsic Dimension(A::ParAxlAlg) -> RngIntElt
  {
  Dimension of the partial algebra.
  }
  return Dimension(A`W);
end intrinsic;

intrinsic BaseField(A::ParAxlAlg) -> Rng
  {
  Base field of the partial algebra.
  }
  return BaseField(A`W);
end intrinsic;

intrinsic Group(A::ParAxlAlg) -> GrpPerm
  {
  Group of the partial algebra.
  }
  return Group(A`Wmod);
end intrinsic;
/*
intrinsic Hash(A::ParAxlAlg) -> RngIntElt
  {
  }
  return Hash(A`W);  
end intrinsic;
*/
intrinsic 'eq'(A::ParAxlAlg, B::ParAxlAlg) -> BoolElt
  {}
  attrs := GetAttributes(ParAxlAlg);
  if not forall{ attr : attr in attrs | assigned A``attr eq assigned B``attr} then
    return false;
  end if;
  for attr in attrs do
    if assigned A``attr and A``attr cmpne B``attr then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic IsEqual(U::ModGrp, V::ModGrp) -> BoolElt
  {}
  if Dimension(U) ne Dimension(V) or BaseRing(U) ne BaseRing(V) or Group(U) ne Group(V) then
    return false;
  end if;
  return ActionGenerators(U) eq ActionGenerators(V);  
end intrinsic;

intrinsic IsEqual(A::SubAlg, B::SubAlg) -> BoolElt
  {}
  attrs := Set(GetAttributes(SubAlg));
  if not forall{ attr : attr in attrs | assigned A``attr eq assigned B``attr} then
    return false;
  end if;
  if A`subsps ne B`subsps then
    return false;
  elif not forall{ i : i in [1..#A`maps] | A`maps[i,2] eq B`maps[i,2] and A`maps[i,3] eq B`maps[i,3]} then
    return false;
  elif not forall{ i : i in [1..#A`maps] | Domain(A`maps[i,1]) eq Domain(B`maps[i,1]) and Image(A`maps[i,1]) eq Image(B`maps[i,1]) and Basis(Domain(A`maps[i,1])) eq Basis(Domain(B`maps[i,1])) and [u@A`maps[i,1] : u in Basis(Domain(A`maps[i,1]))] eq [u@B`maps[i,1] : u in Basis(Domain(B`maps[i,1]))]} then
    return false;
  elif not forall{ i : i in [1..#A`algs] | IsEqual(A`algs[i], B`algs[i])} then
    return false;
  end if;
  return true;
end intrinsic;

intrinsic IsEqual(A::AxlAxis, B::AxlAxis) -> BoolElt
  {}
  attrs := Set(GetAttributes(AxlAxis));
  if not forall{ attr : attr in attrs | assigned A``attr eq assigned B``attr} then
    return false;
  end if;
  for attr in attrs diff {"WH", "id"} do
    if assigned A``attr and A``attr ne B``attr then
      return false;
    end if;
  end for;
  if assigned A`id and A`id`elt ne B`id`elt then
    return false;
  end if;
  return IsEqual(A`WH, B`WH);
end intrinsic;

intrinsic IsEqual(A::ParAxlAlg, B::ParAxlAlg) -> BoolElt
  {}
  attrs := Set(GetAttributes(ParAxlAlg));
  if not forall{ attr : attr in attrs | assigned A``attr eq assigned B``attr} then
    return false;
  end if;
  for attr in attrs diff {"Wmod", "subalgs", "axes"} do
    if assigned A``attr and A``attr ne B``attr then
      return false;
    end if;
  end for;
  
  // Now we need to check the other items
  if not IsEqual(A`Wmod, B`Wmod) then
    return false;
  elif assigned A`subalgs and not IsEqual(A`subalgs, B`subalgs) then
    return false;
  elif #A`axes ne #B`axes or not forall{ i : i in [1..#A`axes] | IsEqual(A`axes[i], B`axes[i])} then;
    return false;
  end if;
  return true;
end intrinsic;

intrinsic Basis(A::ParAxlAlg) -> SeqEnum
  {
  Basis of the A.
  }
  return [ CreateElement(A, v) : v in Basis(A`W)];
end intrinsic;

intrinsic '.'(A::ParAxlAlg, i::RngIntElt) -> ParAxlAlgElt
  {
  Basis of the A.
  }
  bas := Basis(A);
  require i gt 0 and i le #bas: "Argument 2 (", i, ") should be in the range", [1..#bas];
  return Basis(A)[i];
end intrinsic;
/*

intrinsics for partial axial algebra elements

*/
intrinsic Parent(x::ParAxlAlgElt) -> ParAxlAlg
  {
  Parent of x.
  }
  return x`parent;
end intrinsic;

intrinsic Print(x::ParAxlAlgElt)
  {
  Print x.
  }
  printf "%o", x`elt;
end intrinsic;

intrinsic 'eq'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> BoolElt
  {
  Returns whether x is in A.
  }
  require x`parent eq y`parent: "The two elements are not in the same partial axial algebra.";
  return x`elt eq y`elt;
end intrinsic;

intrinsic 'in'(x::ParAxlAlgElt, A::ParAxlAlg) -> BoolElt
  {
  Returns whether x is in A.
  }
  return x`parent eq A;
end intrinsic;

intrinsic 'in'(x::ParAxlAlgElt, U::ModTupFld) -> BoolElt
  {
  Returns whether x is in the subspace U of the partial axial algebra.
  }
  require U subset Parent(x)`W: "U is not a subspace of the axial algebra containing x.";
  return x`elt in U;
end intrinsic;

// maybe this should be a function?
intrinsic CreateElement(A::ParAxlAlg, x::.) -> ParAxlAlgElt
  {
  Creates a element.
  }
  xx := New(ParAxlAlgElt);
  xx`parent := A;
  xx`elt := (A`W)!x;
  
  return xx;
end intrinsic;

intrinsic IsCoercible(A::ParAxlAlg, x::.) -> BoolElt, .
  {
  Returns whether x is coercible into A and the result if so.
  }
  W := A`W;
  if Type(x) eq ParAxlAlgElt and x`parent eq A then
    return true, x;
  end if;
  n := Dimension(W);
  so := false;
  if (Type(x) eq SeqEnum and #x eq n) or Type(x) eq ModTupFldElt then
    so := IsCoercible(W, x);
  elif Type(x) eq ModGrpElt then
    so := IsCoercible(A`Wmod, x);
  elif Type(x) eq RngIntElt and x eq 0 then
    return true, CreateElement(A, [0 : i in [1..Dimension(A)]]);
  end if;

  if not so then
    return false, "Illegal coercion.";
  else
    return true, CreateElement(A, Eltseq(x));
  end if;
end intrinsic;

intrinsic Hash(x::ParAxlAlgElt) -> RngIntElt
  {
  Returns the hash value of x.
  }
  return Hash(x`elt);
end intrinsic;

intrinsic Eltseq(x::ParAxlAlgElt) -> SeqEnum
  {
  Returns the sequence of coefficients of x`elt.
  }
  return Eltseq(x`elt);
end intrinsic;

intrinsic IsZero(x::ParAxlAlgElt) -> BoolElt
  {
  Returns whether an element is zero or not.
  }
  return IsZero(x`elt);
end intrinsic;

intrinsic '+'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> ParAxlAlgElt
  {
  Sums x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same partial axial algebra.";
  return CreateElement(Parent(x), x`elt+y`elt);
end intrinsic;

intrinsic '*'(al::RngElt, x::ParAxlAlgElt) -> ParAxlAlgElt
  {
  Returns the product of al and x.
  }
  require al in BaseRing(Parent(x)`W): "The scalar given in not in the base ring of the algebra.";
  return CreateElement(Parent(x), al*x`elt);
end intrinsic;

intrinsic '*'(x::ParAxlAlgElt, al::RngElt) -> ParAxlAlgElt
  {
  "
  }
  return al*x;
end intrinsic;

intrinsic '*'(x::ParAxlAlgElt, y::ParAxlAlgElt) -> ParAxlAlgElt
  {
  Returns the product of x and y, if it exists.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same partial axial algebra.";
  so, xy := IsTimesable(x, y);
  if so then
    return xy;
  else
    return false;
  end if;
end intrinsic;

intrinsic '*'(x::ParAxlAlgElt, g::GrpPermElt) -> ParAxlAlgElt
  {
  Returns the iamge of x under the action of G.
  }
  A := Parent(x);
  require g in Group(A`Wmod): "g is not a member of the group which acts on the partial axial algebra which contains x.";
  return CreateElement(A, ((A`Wmod)!(x`elt))*g);
end intrinsic;
/*

intrinsics for subalgebras.

*/
intrinsic 'eq'(A::SubAlg, B::SubAlg) -> BoolElt
  {}
  for attr in GetAttributes(SubAlg) do
    if assigned A``attr then
      if not assigned B``attr or not(A``attr cmpeq B``attr) then
        return false;
      end if;
    elif assigned B``attr then
      if not assigned A``attr or not (A``attr cmpeq B``attr) then
        return false;
      end if;
    end if;
  end for;
  return true;
end intrinsic;
/*

intrinsics for axes.

*/
intrinsic 'eq'(A::AxlAxis, B::AxlAxis) -> BoolElt
  {}
  for attr in GetAttributes(AxlAxis) do
    if assigned A``attr then
      if not assigned B``attr or not(A``attr cmpeq B``attr) then
        return false;
      end if;
    elif assigned B``attr then
      if not assigned A``attr or not (A``attr cmpeq B``attr) then
        return false;
      end if;
    end if;
  end for;
  return true;
end intrinsic;
/*
intrinsic 'in'(a:: ModTupFldElt, A::ParAxlAlg) -> BoolElt
  {}
  return a in A`W;
end intrinsic;
*/

intrinsic CheckEigenspaceDimensions(A::ParAxlAlg: U := A`W, empty := false) -> SeqEnum
  {
  Returns the dimensions of the eigenspaces for the idempotents.  Optional argument for intersecting all eigenspaces with U.
  }
  out := [ ];
  if not assigned A`axes then
    return [];
  end if;
  W := A`W;
  for i in [1..#A`axes] do
    subsets := {@ {@ 1 @}, {@ 0 @}, {@ 1/4 @}, {@ 1, 0 @}, {@ 1, 1/4 @}, {@ 0, 1/4 @}, {@ 1, 0, 1/4 @} @};
    if empty then
      subsets := {@ {@@} @} join subsets;
    end if;
    Append(~out, [ Dimension(U meet A`axes[i]`even[s]) : s in subsets ]);
    Append(~out[i], Dimension(U meet A`axes[i]`odd[{@1/32@}]));
  end for;
  return out;
end intrinsic;
/*

Calculates the multiplication in the partial algebra for elements of V.

NB u and v must be in A`V!!

*/
intrinsic Times(u::ParAxlAlgElt, v::ParAxlAlgElt) -> ParAxlAlgElt
  {
  For u and v in V, calculate the product u*v.
  }
  A := Parent(u);
  require A eq Parent(v): "Both elements do not lie in a common partial axial algebra.";
  V := A`V;
  require u in V and v in V: "Cannot multiply elements which are not in V.";
  uu := Coordinates(V, u`elt);
  vv := Coordinates(V, v`elt);
  // could even check to see if product is 0 but will run into trouble with summing over an empty seq
  dim := Dimension(V);
  return CreateElement(A, &+[ A`W | (uu[i]*vv[j] + uu[j]*vv[i])*A`mult[i,j] : i in [j+1..dim], j in [1..dim] | (uu[i] ne 0 and vv[j] ne 0) or (uu[j] ne 0 and vv[i] ne 0)] + &+[ A`W | uu[i]*vv[i]*A`mult[i,i] : i in [1..dim] | uu[i] ne 0 and vv[i] ne 0]);
end intrinsic;
/*

If (conjugates of) two elements of W both lie in a subalgebra in which we can multiply, then we can multiply them in the partial algebra.

*/
//  Coerces v into Wmod, applies g and coerces the result back into the parent vector space of v.
function Image(g, Wmod, v)
  return Parent(v)!((Wmod!v)*g);
end function;

intrinsic IsTimesable(u::ParAxlAlgElt, v::ParAxlAlgElt) -> BoolElt, ParAxlAlgElt
  {
  Tests whether u and v can be multiplied and if so returns their product.
  }
  A := Parent(u);
  require A eq Parent(v): "Both elements do not lie in a common partial axial algebra.";

  if assigned A`V and u in A`V and v in A`V then
    return true, Times(u, v);
  end if;

  W := A`W;
  Wmod := A`Wmod;
  G := Group(Wmod);

  i_subalgs := [ i : i in [1..#A`subalgs`subsps] | exists{ g : g in G | Image(g, Wmod, u`elt) in A`subalgs`subsps[i] and Image(g, Wmod, v`elt) in A`subalgs`subsps[i] }];

  if IsEmpty(i_subalgs) then
    return false, _;
  end if;

  for i in i_subalgs do
    subsp := A`subalgs`subsps[i];
    phi, _, j := Explode(A`subalgs`maps[i]);
    alg := A`subalgs`algs[j];

    gs := [ g : g in G | Image(g, Wmod, u`elt) in subsp and Image(g, Wmod, v`elt) in subsp ];
    for g in gs do
      uu:= Image(g, Wmod, u`elt) @ phi;
      vv:= Image(g, Wmod, v`elt) @ phi;
      so, uv := HasPreimage(Times(alg!uu,alg!vv)`elt, phi);
      if so then
        return true, CreateElement(A, Image(g^-1, Wmod, W!uv));
      end if;
    end for;
  end for;
  return false, _;
end intrinsic;
/*

A handy function for applying a homomorphism to a set/sequence of vectors quickly.  I think it is quicker as magma uses fast matrix multiplication???

*/
intrinsic FastFunction(L::SeqEnum, map::Map:
   matrix := Matrix(BaseRing(Domain(map)), Dimension(Domain(map)), Dimension(Codomain(map)), [U.i@map where U := Domain(map): i in [1..Dimension(Domain(map))]])) -> SeqEnum
  {
  Given a set or sequence of vectors and a homomorphism, returns the sequence which is the application of the map to each.  Uses matrix methods to achieve a speed up.
  }
  if #L eq 0 then
    return [];
  end if;
  require L[1] in Domain(map): "The elements of L must be in the domain of the map.";
  return [ Codomain(map) | v : v in Rows(Matrix(L)*matrix)];
end intrinsic;

intrinsic FastFunction(L::SetIndx, map::Map:
   matrix := Matrix(BaseRing(Domain(map)), Dimension(Domain(map)), Dimension(Codomain(map)), [U.i@map where U := Domain(map): i in [1..Dimension(Domain(map))]])) -> SetIndx
  {
  Given a set or sequence of vectors and a homomorphism, returns the set which is the application of the map to each.  Uses matrix methods to achieve a speed up.
  }
  if #L eq 0 then
    return [];
  end if;
  require L[1] in Domain(map): "The elements of L must be in the domain of the map.";
  return {@ Codomain(map) | v : v in Rows(Matrix(Setseq(L))*matrix)@};
end intrinsic;

intrinsic FastMatrix(L::SeqEnum, matrix::.) -> SeqEnum
  {
  Given a set or sequence of vectors and a matrix, returns the sequence which is the application of the matrix to each.  Uses matrix methods to achieve a speed up.
  }
  require Type(matrix) in {ModMatFldElt, AlgMatElt, GrpMatElt}: "You have not given a valid matrix.";
  if #L eq 0 then
    return [];
  end if;
  return [ v : v in Rows(Matrix(L)*matrix)];
end intrinsic;

intrinsic FastMatrix(L::SetIndx, matrix::.) -> SetIndx
  {
  Given a set or sequence of vectors and a homomorphism, returns the set which is the application of the matrix to each.  Uses matrix methods to achieve a speed up.
  }
  require Type(matrix) in {ModMatFldElt, AlgMatElt, GrpMatElt}: "You have not given a valid matrix.";
  if #L eq 0 then
    return {@@};
  end if;
  return {@ v : v in Rows(Matrix(Setseq(L))*matrix)@};
end intrinsic;
/*

We now provide functions for fast multiplication of an element by a collection of elements or of two collections of elements together.  This uses the fast matrices above.

*/
intrinsic FastMultiply(L::SeqEnum, v::ParAxlAlgElt) -> SeqEnum
  {
  Given a sequence L of vectors, partial axial algebra elements, or sequences of coordinates in V, return the product of these with the partial axial algebra element v.
  }
  A := Parent(v);
  V := A`V;
  require v`elt in V: "The element given is not in V.";
  if #L eq 0 then
    return [];
  elif IsZero(v) then
    return [ A!0 : i in [1..#L]];
  end if;
  
  vv := Coordinates(V, v`elt);
  mat := &+[ Matrix( [vv[i]*A`mult[j,i] : j in [1..Dimension(V)]]) : i in [1..Dimension(V)] | vv[i] ne 0];
  
  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, SeqEnum}: "The list given is not in a partial alxial algebra.";
  if Type(L[1]) eq ParAxlAlgElt then
    L := [ l`elt : l in L];
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
    return [ A!u : u in FastMatrix(L, mat)];
  elif Type(L[1]) eq ModTupFldElt then
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
  end if;
  
  return FastMatrix(L, mat);
end intrinsic;

intrinsic FastMultiply(A::ParAxlAlg, L::SeqEnum, v::ModTupFldElt) -> SeqEnum
  {
  Given a sequence L of vectors, partial axial algebra elements, or sequences of coordinates in V, return the product of these with the partial axial algebra element of A represented by v.
  }
  require IsCoercible(A,v): "The element given does not represent an element of A.";
  V := A`V;
  require v in V: "The element given is not in V.";
  if #L eq 0 then
    return [];
  elif IsZero(v) then
    return [ A`W!0 : i in [1..#L]];
  end if;

  vv := Coordinates(V, v);
  mat := &+[ Matrix( [vv[i]*A`mult[j,i] : j in [1..Dimension(V)]]) : i in [1..Dimension(V)] | vv[i] ne 0];

  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, SeqEnum}: "The list given is not in a partial alxial algebra.";
  if Type(L[1]) eq ParAxlAlgElt then
    L := [ l`elt : l in L];
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
    return [ A!u : u in FastMatrix(L, mat)];
  elif Type(L[1]) eq ModTupFldElt then
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
  end if;
  
  return FastMatrix(L, mat);
end intrinsic;

intrinsic FastMultiply(A::ParAxlAlg, L::SeqEnum, v::SeqEnum) -> SeqEnum
  {
  Given a sequence L of vectors, partial axial algebra elements, or sequences of coordinates in V, return the product of these with the partial axial algebra element of A represented by v.
  }
  V := A`V;
  require #v eq Dimension(V): "The element given does not represent an element of A in V.";
  if #L eq 0 then
    return [];
  elif Set(v) eq {0} or #v eq 0 then
    return [ A`W!0 : i in [1..#L]];
  end if;

  mat := &+[ Matrix( [v[i]*A`mult[j,i] : j in [1..Dimension(V)]]) : i in [1..Dimension(V)] | v[i] ne 0];

  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, SeqEnum}: "The list given is not in a partial alxial algebra.";
  if Type(L[1]) eq ParAxlAlgElt then
    L := [ l`elt : l in L];
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
    return [ A!u : u in FastMatrix(L, mat)];
  elif Type(L[1]) eq ModTupFldElt then
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
  end if;

  return FastMatrix(L, mat);
end intrinsic;
/*

Calculate the batches of multiplications quickly

*/
intrinsic BulkMultiply(A::ParAxlAlg, L::SeqEnum) -> SeqEnum
  {
  Calculate the multiplication in A of L with L.  Returns a single sequence of vectors representing one half of the multiplications L[1]*L[1], L[2]*L[1], L[2]*L[2], L[3]*L[1] etc.
  }
  V := A`V;
  if #L eq 0 then
    return [];
  elif Dimension(V) eq 0 then
    return [ A`W!0 : i in [1..(#L*(#L+1) div 2)]];
  end if;
  
  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, SeqEnum}: "The elements given do not represent elements of A.";
  if Type(L[1]) eq ParAxlAlgElt then
    require Universe(L) eq A and forall{ l : l in L | l`elt in V}: "The list of elements given are not in V.";
    L := [ Coordinates(V, l`elt) : l in L];
  elif Type(L[1]) eq ModTupFldElt then
    require forall{ l : l in L | l in V}: "The list of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
  end if;

  return &cat [ FastMultiply(A, L[1..i], L[i]) : i in [1..#L]];
end intrinsic;

intrinsic BulkMultiply(A::ParAxlAlg, L::SeqEnum, M::SeqEnum) -> SeqEnum
  {
  Calculate the multiplication in A of all elements of L with M.  Returns a sequence of sequences of vectors representing L[1]*M, L[2]*M etc.
  }
  V := A`V;
  if #M eq 0 then
    return [];
  elif #L eq 0 then
    return [ [] : m in M];
  end if;
  
  require Type(L) eq Type(M): "The two lists have different types.";
  require Type(L[1]) in {ParAxlAlgElt, ModTupFldElt, SeqEnum}: "The elements given do not represent elements of A.";
  if Type(L[1]) eq ParAxlAlgElt then
    require Universe(L) eq A and Universe(M) eq A and forall{ l : l in L | l`elt in V} and forall{ m : m in M | m`elt in V}: "The lists of elements given are not in V.";
    L := [ Coordinates(V, l`elt) : l in L];
    M := [ Coordinates(V, m`elt) : m in M];
  elif Type(L[1]) eq ModTupFldElt then
    require forall{ l : l in L | l in V} and forall{ m : m in M | m in V}: "The lists of elements given are not in V.";
    L := [Coordinates(V, l) : l in L];
    M := [Coordinates(V, m) : m in M];
  end if;
  
  // We minimise the number of matrix operations.
  if #L lt #M then
    mult := [ FastMultiply(A, M, L[i]) : i in [1..#L]];
    return [[ mult[i,j] : i in [1..#L]] : j in [1..#M]];
  else
    return [ FastMultiply(A, L, M[i]) : i in [1..#M]];
  end if;
end intrinsic;

intrinsic BulkMultiply(mult::SeqEnum, I1::SeqEnum, I2::SeqEnum) -> SeqEnum
  {
  Let mult be an nxk array with entries being m-dimensional vectors representing the multiplication of a n-dimensional by a k-dimensional space.  I1 and I2 are sequences of inputs in the n-dimensional and k-dimensional spaces respectively.
  }
  // Could speed this up even more by optimising the number of matrix multiplications to be done.  Either k+a, or n+b?
  // can we eliminate some tr?
  if #mult eq 0 or #I1 eq 0 then
    return [];
  elif #mult[1] eq 0 or #I2 eq 0 then
    return [ [] : i in I1];
  end if;
  I1 := Matrix(I1);
  I2 := Transpose(Matrix(I2));
  a := NumberOfRows(I1);
  n := NumberOfColumns(I1);
  k := NumberOfRows(I2);
  b := NumberOfColumns(I2);
  m := Degree(mult[1,1]);

  // View mult as a list of k nxm matrices  
  mats := [ Matrix([mult[i,j] : i in [1..n]]) : j in [1..k]];
  out := [ I1*M : M in mats];
  
  // Now we have k axm matrices, we reform them as a mxk matrices
  out := [ Transpose(Matrix([ out[j,i] : j in [1..k]])) : i in [1..a]];
  out := [ Transpose(M*I2) : M in out];
  
  // We have a bxm matrices, we reform these into a single axb array whose entries are m-dimensional vectors
  return [[ out[i,j] : j in [1..b] ] : i in [1..a]];
end intrinsic;


/*

A function for returning the axes together with the tau map

*/
intrinsic Axes(A::ParAxlAlg) -> SetIndx, Map
  {
  Returns the set of Axes of A and the tau map from the axes to the involutions of the Miyamoto group of A.
  }
  all_pairs := {@ @};
  if not assigned A`axes then
    return {@ @}, _;
  end if;
  for i in [1..#A`axes] do
    pairs := {@ <A`axes[i]`id*g, A`axes[i]`inv^g> : g in Group(A) @};
    Sort(~pairs, func<x,y| x[1]`elt lt y[1]`elt select 1 else x[1]`elt eq y[1]`elt select 0 else -1>);
    Include(~all_pairs, pairs);
  end for;
  axes := &join{@ {@ pair[1] : pair in pairs @} : pairs in all_pairs @};
  tau := map<axes -> Group(A) | Set(&join all_pairs)>;
  
  return axes, tau;
end intrinsic;


// ***Need to correct!!***
intrinsic mClosed(A::ParAxlAlg) -> RngIntElt
  {
  Need to correct!!!
  }
  require A`V eq A`W: "Can't calculate m-closed before calculating the algebra!.";
  if Dimension(A) eq 0 then
    return 0;
  end if;
  G := Group(A);
  W := A`W;
  axes := &join{@ {@ A`axes[i]`id*g : g in G @} : i in [1..#A`axes] @};
  
  U := sub<W|[ a`elt : a in axes]>;
  products := axes;
  m := 1;
  while Dimension(U) ne Dimension(W) do
    products := [ u*v : u in products, v in axes ];
    U +:= sub<W| [ x`elt : x in products]>;
    products := [ A!u : u in Basis(U)];
    m +:=1;
  end while;
  
  return m;
end intrinsic;
/*
intrinsic SubConstructor(A::ParAxlAlg, tup) -> ParAxlAlg
  {}
  G := Group(A);
  require Type(tup[1]) eq GrpPerm and tup[1] subset G: "You have not provided a group";
  H := tup[1];
  S := {@ A| tup[i] : i in [2..#tup]@};
  Asub := New(ParAxlAlg);
  
  WH := Restriction(A`Wmod, H);
  Asub`Wmod := sub< WH | [ WH!(s`elt) : s in S]>;
  Asub`W := GInvariantSubspace(WH, S);
  return Asub;
end intrinsic;
*/