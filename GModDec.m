/*

Package for G-modules in magma to make use of the decomposition

Authors: Justin McInroy, Sergey Shpectorov
With thanks to Dmitrii Pasechnik
*/

/*
=======  Background  =======

Suppose W is a semisimple G-module (always true in char 0, or where the characteristic doesn't divide |G|)

W \cong U_1^1 \oplus ... \oplus U_1^{k_1} \oplus ... \oplus U_n^1 \oplus ... \oplus U_n^{k_n}

where the set of different irreducible constituents of W are U_1, ..., U_n and these have multiplicity k_1, ..., k_n.

Note that

U_i^1 \oplus ... \oplus U_i^{k_i} \cong \mathbb{F}^{k_i} \otimes U_i

We wish to represent W as

M = \bigoplus_{i=1}^n \mathbb{F}^{k_i} \otimes U_i

In particular, elements of \mathbb{F}^{k_i} \otimes U_i are just k_i x Dimension(U_i) matrices and finding the submodule spanned by such elements is just taking the column span

*/
declare type GModDec[GModDecElt];

declare attributes GModDec:
  group,              // The group G
  irreducibles,       // A SeqEnum of all the irreducibles for the group G
  multiplicities,     // A SeqEnum of the multiplicities of each irreducible
  subspaces,          // A SeqEnum of vector spaces of the corresponding multiplicity
  tensors,            // ?? A SeqEnum of SeqEnums of the tensor products of the irreducibles
  symmetric_squares;  // ?? A SeqEnum of the symmetric squares of the irreducibles

// NB Not sure quite how to save the info for tensors and symmetric_squares yet.  Need both a seq of multiplicities for each and the maps mapping the tensor to our representation of it.
  
declare attributes GModDecElt:
  parent,           // Parent
  elt;              // A List of matrices, one for each irreducible.
  
/*

=======  Functions for a GModDec  =======

*/
intrinsic Print(M::GModDec)
  {
  Prints a GModDec.
  }
  printf "A DecomposedGModule of dimension %o over %o", Dimension(M), BaseRing(M);
end intrinsic;

intrinsic Group(M::GModDec) -> Grp
  {
  The group G of the G-module M.
  }
  return M`group;
end intrinsic;

intrinsic Dimension(M::GModDec) -> RngIntElt
  {
  Dimension of the module.
  }
  return &+[ M`multiplicities[i]*Dimension(M`irreducibles[i]) : i in [1..#M`multiplicities] | M`multiplicities[i] ne 0];
end intrinsic;

intrinsic BaseRing(M::GModDec) -> Rng
  {
  Base ring of the module.
  }
  return BaseRing(M`irreducibles[1]);
end intrinsic;
/*

=======  Creating a GModDecs  =======

*/
intrinsic DecomposedGModule(M::ModGrp) -> GModDec, Mtrx
  {
  The GModDec of the magma G-module M.
  }
  G := Group(M);
  F := BaseRing(M);
  
  N := New(GModDec);
  N`group := G;
  N`irreducibles := IrreducibleModules(G, F);
  
  if F eq Rationals() then
    T := RationalCharacterTable(G);
    char := Character(M);
    N`multiplicities := ChangeUniverse(Decomposition(T, char), Integers());
    dec := Decomposition(M);
  else
    dec := Decomposition(M);
    iso_class := {* i where so := exists(i){i : i in [1..#N`irreducibles] | IsIsomorphic(U, N`irreducibles[i])} : U in dec *};
    N`multiplicities := ChangeUniverse([ Multiplicity(iso_class, i) : i in [1..#N`irreducibles]], Integers());
  end if;
    
  N`subspaces := [ VectorSpace(F, d) : d in N`multiplicities ];

  N`tensors := [ [] : i in [1..#N`irreducibles]];
  N`symmetric_squares := [];
  
  S := MultisetToSequence({* i^^N`multiplicities[i] : i in [1..#N`irreducibles]*});
  CoB := Matrix([ VectorSpace(M) | M!u : u in Basis(U), U in dec])^-1 *
           DiagonalJoin(< iso where so, iso := IsIsomorphic(dec[i], N`irreducibles[S[i]]) : i in [1..#dec]>);
  
  return N, CoB;
end intrinsic;

intrinsic DecomposedGModule(S::SeqEnum[Mtrx]) -> GModDec
  {
  Returns the decomposed G-module generated by the matrices in S.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;
/*

=======  Building new GModDecs out of old ones  =======

*/
intrinsic SubConstructor(M::GModDec, X::.) -> GModDec
  {
  The submodule generated by X.
  }
  XX := { M | x : x in X };
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  Mnew`subspaces := [ sub< M`subspaces[i] | Flat([ Rows(Transpose(x`elt[i])) : x in XX])> : i in [1..#M`irreducibles]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;

intrinsic QuoConstructor(M::GModDec, X::.) -> GModDec, SeqEnum[Map]
  {
  The quotient of M by the submodule generated by X and also a sequence of quotient maps.
  }
  XX := { M | x : x in X };
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  quos := [ < Q, psi> where Q, psi := quo< M`subspaces[i] | Flat([ Rows(Transpose(x`elt[i])) : x in XX])> : i in [1..#M`irreducibles]];
  
  Mnew`subspaces := [ t[1] : t in quos];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew, [ t[2] : t in quos];
end intrinsic;

/*

Given a sequence Q of sequences, produce the merged version.
Will be used for tensor and symmetric_square attributes

NB elements in the sequence may be undefined, but where they are defined, they must agree.

*/
function Merge(Q)
  L := [];
  for i in [1..Maximum([#S : S in Q])] do
    if exists(S){S : S in Q | IsDefined(S, i)} then
      L[i] := S[i];
    end if;
  end for;

  return L;
end function;

intrinsic DirectSum(M::GModDec, N::GModDec) -> GModDec, SeqEnum, SeqEnum, SeqEnum, SeqEnum
  {
  The direct sum of M and N, the two inclusion maps and the two projection maps.
  }
  require Group(M) eq Group(N) and BaseRing(M) eq BaseRing(N): "The two modules must be for the same group and over the smae field.";
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  
  Mnew`tensors := [ Merge([M`tensors[i], N`tensors[i]]) : i in [1..#M`irreducibles]];
  Mnew`symmetric_squares := Merge([ M`symmetric_squares, N`symmetric_squares]);
  
  sums := [ < V, inj1, inj2, proj1, proj2 > 
      where V, inj1, inj2, proj1, proj2 := DirectSum(M`subspaces[i], N`subspaces[i])
                   : i in [1..#M`irreducibles]];
  
  Mnew`subspaces := [ t[1] : t in sums ];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  maps := [ [ t[i] : t in sums ] : i in [2..5]];
  inj1, inj2, proj1, proj2 := Explode(maps);
  // Don't know how to form maps between objects of our new type
  // Can magma even do this???
  // For now, we return a sequence of maps, one for each homogeneous component.
  return Mnew, inj1, inj2, proj1, proj2;
end intrinsic;

intrinsic DirectSum(Q::SeqEnum[GModDec]) -> GModDec, SeqEnum, SeqEnum
  {
  The direct sum of the modules in Q, a sequence of inclusion maps and a sequence of projection maps.
  }
  require forall{ M : M in Q | Group(M) eq Group(Q[1])} and forall{ M : M in Q | BaseRing(M) eq BaseRing(Q[1])}: "The modules must be for the same group and over the smae field.";
  Mnew := New(GModDec);
  Mnew`group := Q[1]`group;
  Mnew`irreducibles := Q[1]`irreducibles;
  
  Mnew`tensors := [ Merge([M`tensors[i] : M in Q]) : i in [1..#Mnew`irreducibles]];
  Mnew`symmetric_squares := Merge([ M`symmetric_squares : M in Q]);
  
  sums := [ < V, injs, projs > 
      where V, injs, projs := DirectSum([ M`subspaces[i] : M in Q])
                   : i in [1..#Mnew`irreducibles]];
  
  Mnew`subspaces := [ t[1] : t in sums ];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  injs := [ [ t[2,i] : t in sums] : i in [1..#Q]];
  projs := [ [ t[3,i] : t in sums] : i in [1..#Q]];
  // Don't know how to form maps between objects of our new type
  // Can magma even do this???
  // For now, we return a sequence of maps, one for each homogeneous component.
  return Mnew, injs, projs;
end intrinsic;

intrinsic TensorProduct(M::GModDec, N::GModDec) -> GModDec
  {
  The tensor product of M and N.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic SymmetricSquare(M::GModDec) -> GModDec
  {
  The symmetric square of M.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic Restriction(M::GModDec, H::Grp) -> GModDec
  {
  Returns the restriction of the G-module M to an H-module where H is a subgroup of G.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic ChangeField(M::GModDec, F::Fld) -> GModDec
  {
  Returns the module defined over the field F.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic ChangeRing(M::GModDec, R::Rng) -> GModDec
  {
  Returns the module defined over the ring R.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic Moduli(M::GModDec) -> SeqEnum
  {
  The column moduli of the module M over a euclidean domain.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;
/*

=======  Functions on submodules of GModDecs  =======

*/
intrinsic Generic(M::GModDec) -> GModDec
  {
  The module which contains M as a submodule.
  }
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  Mnew`subspaces := [ Generic(V) : V in M`subspaces ];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;

intrinsic 'eq'(M::GModDec, N::GModDec) -> BoolElt
  {
  Equality of two submodules M and N.
  }
  require M`group eq N`group and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #M`irreducibles eq # N`irreducibles;
  
  return forall{ i : i in [1..#M`irreducibles] | M`subspaces[i] eq N`subspaces[i]};
end intrinsic;

intrinsic IsIsomorphic(M::GModDec, N::GModDec) -> BoolElt, Map
  {
  Returns whether M and N are isomorphic and if so also returns the ismomorphism.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic 'subset'(N::GModDec, M::GModDec) -> BoolElt
  {
  Whether N is a submodule of M.
  }
  require M`group eq N`group and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #M`irreducibles eq # N`irreducibles;
  
  return forall{ i : i in [1..#N`irreducibles] | N`subspaces[i] subset M`subspaces[i]};
end intrinsic;

intrinsic '+'(M::GModDec, N::GModDec) -> GModDec
  {
  The sum of the two submodules M and N.
  }
  require M`group eq N`group and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #M`irreducibles eq # N`irreducibles;
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  Mnew`subspaces := [ M`subspaces[i] + N`subspaces[i] : i in [1..#M`irreducibles]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;

intrinsic 'meet'(M::GModDec, N::GModDec) -> GModDec
  {
  The intersection of two submodules M and N.
  }
  require M`group eq N`group and BaseRing(M) eq BaseRing(N): "There is no covering module.";
  assert #M`irreducibles eq # N`irreducibles;
  
  Mnew := New(GModDec);
  Mnew`group := M`group;
  Mnew`irreducibles := M`irreducibles;
  Mnew`tensors := M`tensors;
  Mnew`symmetric_squares := M`symmetric_squares;
  
  Mnew`subspaces := [ M`subspaces[i] meet N`subspaces[i] : i in [1..#M`irreducibles]];
  Mnew`multiplicities := [ Dimension(V) : V in Mnew`subspaces];
  
  return Mnew;
end intrinsic;
/*

=======  Translating between different structures  =======

*/
intrinsic GModule(M::GModDec) -> ModGrp
  {
  The magma G-module given by M.
  }
  return DirectSum(Flat([ [ M`irreducibles[i] : j in [1..M`multiplicities[i]]] : i in [1..#M`irreducibles]]));
end intrinsic;

intrinsic VectorSpace(M::GModDec) -> ModTupRng
  {
  The vector space defined by M.
  }
  return VectorSpace(BaseRing(M), Dimension(M));
end intrinsic;
/*

=======  GModDecElts  =======

*/
intrinsic Parent(x::GModDecElt) -> GModDec
  {
  Parent of x.
  }
  return x`parent;
end intrinsic;

intrinsic Print(x::GModDecElt)
  {
  Print x.
  }
  printf "%o", x`elt;
end intrinsic;

intrinsic 'eq'(x::GModDecElt, y::GModDecElt) -> BoolElt
  {
  Equality of elements.
  }
  require x`parent eq y`parent: "The two elements are not in the same module.";
  return x`elt eq y`elt;
end intrinsic;

intrinsic 'in'(x::GModDecElt, M::GModDec) -> BoolElt
  {
  Returns whether x is in M.
  }
  return forall{ i : i in [1..#M`multiplicities] | x`elt[i] in M`subspaces[i]};
end intrinsic;

intrinsic Hash(x::GModDecElt) -> RngIntElt
  {
  Returns the hash value of x.
  }
  return Hash(<Group(x`parent), x`elt>);
end intrinsic;

// Is this really needed?
intrinsic Eltseq(x::GModDecElt) -> SeqEnum
  {
  Returns the sequence of coefficients of x`elt.
  }
  return Flat([ RowSequence(x`elt[i]) : i in [1..#x`elt]]);
end intrinsic;

intrinsic Vector(x::GModDecElt) -> ModTupFld
  {
  Returns the vector.
  }
  return Vector(Flat([ RowSequence(x`elt[i]) : i in [1..#x`elt]]));
end intrinsic;

intrinsic IsZero(x::GModDecElt) -> BoolElt
  {
  Returns whether an element is zero or not.
  }
  return forall{ M : M in x`elt | IsZero(M)};
end intrinsic;

function CreateElement(M, x)
  xx := New(GModDecElt);
  xx`parent := M;
  xx`elt := x;
  return xx;
end function;

intrinsic IsCoercible(M::GModDec, x::.) -> BoolElt, GModDecElt
  {
  Returns whether x is coercible into A and the result if so.
  }
  if Type(x) eq List and #x eq #M`irreducibles and
      forall{ x[i] : i in [1..#x] |
         ISA(Type(x[i]), Mtrx) and
         NumberOfColumns(x[i]) eq Dimension(M`irreducibles[i])}
   then
    return true, CreateElement(M, x);
  elif (Type(x) eq SeqEnum and #x eq Dimension(M)) or
     (Type(x) eq ModTupFldElt and Degree(x) eq Dimension(M)) then
    seq := Partition([1..Dimension(M)], [ M`multiplicities[i]*Dimension(M`irreducibles[i]) : i in [1..#M`multiplicities]]);
    xx := [* Matrix(BaseRing(M), M`multiplicities[i], Dimension(M`irreducibles[i]), x[seq[i]]) : i in [1..#seq]*];
    return true, CreateElement(M, xx);
  // COMPLETE SOME MORE CASES
  else
    return false, "Illegal coercion.";
  end if;
end intrinsic;

intrinsic Zero(M::GModDec) -> GModDecElt
  {
  Returns the zero element of M.
  }
  return CreateElement(M, [* Matrix(BaseRing(M), 0, Dimension(U), []) : U in M`irreducibles*]);
end intrinsic;

intrinsic Basis(M::GModDec) -> SeqEnum
  {
  Basis of the module.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;

intrinsic '.'(M::GModDec, i::RngIntElt) -> GModDecElt
  {
  The ith basis element of the module.
  }
  // NOT YET IMPLMENTED
  // return null;
end intrinsic;
/*

=======  Operations on GModDecElts  =======

*/
intrinsic '+'(x::GModDecElt, y::GModDecElt) -> GModDecElt
  {
  Sums x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same module.";
  return CreateElement(Parent(x), [* x`elt[i]+y`elt[i] : i in [1..#x`elt]*]);
end intrinsic;

intrinsic '-'(x::GModDecElt) -> GModDecElt
  {
  Negation of the input.
  }
  return CreateElement(Parent(x), [* -m : m in x`elt*]);
end intrinsic;

intrinsic '-'(x::GModDecElt, y::GModDecElt) -> GModDecElt
  {
  Subtracts x and y.
  }
  require Parent(x) eq Parent(y): "x and y are not in the same module.";
  return CreateElement(Parent(x), [* x`elt[i]-y`elt[i] : i in [1..#x`elt]*]);
end intrinsic;

intrinsic '*'(al::RngElt, x::GModDecElt) -> GModDecElt
  {
  Returns the product of al and x.
  }
  require al in BaseRing(Parent(x)): "The scalar given is not in the base ring of the module.";
  return CreateElement(Parent(x), [* al*m : m in x`elt*]);
end intrinsic;

intrinsic '*'(x::GModDecElt, al::RngElt) -> GModDecElt
  {
  "
  }
  return al*x;
end intrinsic;

intrinsic '/'(x::GModDecElt, al::RngElt) -> GModDecElt
  {
  Returns x divided by al.
  }
  require al in BaseRing(Parent(x)): "The scalar given is not in the base ring of the module.";
  return CreateElement(Parent(x), [* m/al : m in x`elt*]);
end intrinsic;

intrinsic '*'(x::GModDecElt, g::GrpElt) -> GModDecElt
  {
  The image of x under the action of g.
  }
  M := Parent(x);
  require g in Group(M): "g is not a member of the group which acts on the module containing x.";
  // This is probably quicker than coercing each row into U, doing u*g and then reforming a matrix.  Especially as the number of rows grows.
  return CreateElement(M, [* x[i]*(g@GModuleAction(M`irreducibles[i])) : i in [1..#x`elt] *]);
end intrinsic;
