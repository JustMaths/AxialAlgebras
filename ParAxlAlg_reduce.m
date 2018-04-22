/*

Axial algebra enumerator

These are functions to reduce the algebra

*/
import "ParAxlAlg.m": library_location;
/*

This function implements an automatic version of the algorithm:

1) ExpandSpace

2) i) ExpandOdd

  ii) ExpandEven

Check to see if Dim(V) = Dim(W) and if not goto (1) and repeat.

There is a dimension limit where if W exceeds this then it won't be expanded further the procedure exits

*/
intrinsic AxialReduce(A::ParAxlAlg: dimension_limit := 150, saves:=true) -> ParAxlAlg, BoolElt
  {
  Performs ExpandOdd, ExpandEven and ExpandSpace repeatedly until either we have completed, or the dimension limit has been reached.
  }
  if Dimension(A) eq 0 then
    return A;
  end if;

  while Dimension(A) ne Dimension(A`V) and Dimension(A) le dimension_limit do
    A := ExpandSpace(A);
    A := ExpandOdd(A);
    A := ExpandEven(A);
  end while;

  if Dimension(A) eq Dimension(A`V) then
    vprint ParAxlAlg, 1: "Reduction complete!";
    return A, true;
  else
    vprintf ParAxlAlg, 1: "Reduction failed. Dimension of A is %o, dimension of V is %o.\n", Dimension(A), Dimension(A`V);
    return A, false;
  end if;
end intrinsic;
/*

We provide a function to do all shapes for a given group

*/
intrinsic ShapeReduce(G::Grp: dimension_limit := 150, saves:=true, starting_position := 1, fusion_table := MonsterFusionTable(), maximal_subgroups:=true, field:= Rationals()) -> SeqEnum
  {
  Given a group G, find all the shapes, build the partial algebras and reduce.
  }
  shapes := Shapes(G);
  require starting_position le #shapes: "Starting position is greater than the number of shapes.";
  vprintf ParAxlAlg, 1: "Found %o shapes for the group.\n", #shapes;
  output := [];
  for i in [starting_position..#shapes] do
    vprintf ParAxlAlg, 1: "Beginning shape %o of %o.\n", i, #shapes;
    vprintf ParAxlAlg, 1: "Partial algebra has %o axes of shape %o.\n", #shapes[i,1], shapes[i,3];
    A := PartialAxialAlgebra(shapes[i]: fusion_table:=fusion_table, maximal_subgroups:=maximal_subgroups, field:=field);
    t := Cputime();
    A := AxialReduce(A: dimension_limit := dimension_limit);
    Append(~output, A);
    vprintf ParAxlAlg, 4: "\nTime taken for complete reduction %o.\n\n", Cputime(t);
    if saves then
      SavePartialAxialAlgebra(A);
    end if;
  end for;

  return output;
end intrinsic;
// ---------------------------------------------
/*

U is a subspace which we want to mod out by.  Therefore we may also mod out by v*u for any u in U and v in V.  We grow the subspace U by doing this.

*/
intrinsic SaturateSubspace(A::ParAxlAlg, U::ModTupFld: starting := sub<A`W|>) -> ModTupFld
  {
  Add products of U \cap V with V to U until it saturates, also using the action of G.  Has an optional argument of a starting subspace which we assume to be saturated.
  }
  t := Cputime();
  // The expensive part is doing coercion from a G-submod to Wmod in order to coerce into W
  // We minimise the amount of coercion by working in the G-submods as much as possible and only coercing all the vectors in U - U\cap V at the very end.
  
  W := A`W;
  require U subset W: "The given U is not a subspace of W.";
  Wmod := A`Wmod;
  V := A`V;
  time Vmod := sub<Wmod | [ v : v in Basis(V)]>;
  
  time Umod := sub<Wmod| Basis(U)>;
  time Dmod_old := sub<Wmod| Basis(starting meet V)>;
  time Dmod_new := Umod meet Vmod;
  
  // Vbas := Basis(V);
  
  while Dimension(Dmod_new) gt Dimension(Dmod_old) do
    vprintf ParAxlAlg, 1: "Saturate subspace: Dimension intersection with V is %o\n", Dimension(Dmod_new);
    tt := Cputime();
    // We only do products of V with the new vectors found in D
    bas_new := ExtendBasis(Dmod_old, Dmod_new)[Dimension(Dmod_old)+1..Dimension(Dmod_new)];
    
    bas_new := [ W | W!(Wmod!u) : u in bas_new];
    
    print "time for products is";
    time S := {@ (A!u*A!v)`elt : u in bas_new, v in Basis(V) @};
    time SS := BulkMultiply(A, bas_new, Basis(V));
    assert Set(S) eq Set(&cat SS);
    
    print "time for subspace is";
    time Umod +:= sub<Wmod| S>;
    
    Dmod_old := Dmod_new;
    time Dmod_new := Umod meet Vmod;
    vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  end while;
  
  time U := sub<W | [W | W!(Wmod!u) : u in Basis(Umod)]>;
  print "Building morphism, map and mapping elements.";
  time inc := Morphism(Umod, Wmod);
  time Unew := sub<W | [ W | Umod.i*inc : i in [1..Dimension(Umod)]]>;
  assert U eq Unew;
  
  vprintf ParAxlAlg, 4: "Time taken for saturate subspace %o\n", Cputime(t);
  return U;
end intrinsic;

intrinsic OldSaturateSubspace(A::ParAxlAlg, U::ModTupFld: check_is_timesable:=false) -> ModTupFld
  {
  Add products of U \cap V with V to U until it saturates, also using the action of G.
  }
  t := Cputime();
  W := A`W;
  require U subset W: "The given U is not a subspace of W.";
  V := A`V;
  U := GInvariantSubspace(A`Wmod, W, Basis(U));
  D_old := sub<W|>;
  D_new := U meet V;

  while Dimension(D_new) gt Dimension(D_old) do
    vprintf ParAxlAlg, 1: "Saturate subspace: Dimension intersection with V is %o\n", Dimension(D_new);
    // We only do products of V with the new vectors found in D
    bas_new := ExtendBasis(D_old, D_new)[Dimension(D_old)+1..Dimension(D_new)];
    S := {@ u : u in Basis(U) @} join {@ (A!u*A!v)`elt : u in bas_new, v in Basis(V) @};
    U := GInvariantSubspace(A`Wmod, W, S);
    D_old := D_new;
    D_new := U meet V;
  end while;

  vprintf ParAxlAlg, 4: "Time taken for saturate subspace %o\n", Cputime(t);
  return U;
end intrinsic;

intrinsic ReduceSaturated(A::ParAxlAlg, U::ModTupFld) -> ParAxlAlg, Map
  {
  Construct the algebra G-module W/U for a saturated U.
  }
  t := Cputime();
  W := A`W;
  Wmod := A`Wmod;
  V := A`V;
  
  // We must check whether the we are quotienting out anything in the subalgebras
  // If so, then we form the subalgebra quotients, pull back any relations and add them to U

  if assigned A`subalgs then
    tt := Cputime();
    // We create new algebras and maps as we might have to change the algebras to quotients.
    newalgs := A`subalgs`algs;
    newmaps := A`subalgs`maps;
    
    subalgs_intersections := { i : i in [1..#newmaps] | not (A`subalgs`subsps[i] meet U) subset Kernel(newmaps[i,1])};
    extras := sub<W|>;
    while subalgs_intersections ne {} do
      for i in subalgs_intersections do
        subsp := A`subalgs`subsps[i];
        map, homg, pos := Explode(newmaps[i]);
        alg := newalgs[pos];
        
        U_alg := (U meet subsp)@map;
        
        U_alg := SaturateSubspace(alg, U_alg);
        vprint ParAxlAlg, 3: "Reducing the subalgebra.";
        alg_new, quo_alg := ReduceSaturated(alg, U_alg);

        if Dimension(alg_new) eq 0 then
          // We have killed the entire subalgebra and hence modded out A by some axes.
          Anew := New(ParAxlAlg);
          Wnew, psi := quo<W | W>;
          Anew`W := Wnew;
          Anew`Wmod := quo<Wmod | Wmod >;
          Anew`V := V @ psi;
          Anew`fusion_table := A`fusion_table;
          Anew`shape := {@ <{@ i - Dimension(A) : i in sh[1] @}, sh[2]>
                              : sh in A`shape @};
          Anew`number_of_axes := A`number_of_axes;
          vprintf ParAxlAlg, 4: "Time taken for ReduceSaturated %o\n", Cputime(t);
          return Anew, psi;
        else
          // There is a non-trivial quotient of the subalgebra
          newalgs[pos] := alg_new;
          newmaps[i] := < map*quo_alg, homg, pos>;
          
          // We pull back any new relations from the subalgebra
          extras +:= Kernel(quo_alg) @@ map;
        end if;
      end for;
      if Dimension(extras) gt 0 then
        U := SaturateSubspace(A, U+extras: starting := U);
      end if;
      subalgs_intersections := { i : i in [1..#newmaps] | not (A`subalgs`subsps[i] meet U) subset Kernel(newmaps[i,1])};
    end while;
    
    vprintf ParAxlAlg, 4: "Time taken for collecting info from subalgebras %o\n", Cputime(tt);
  end if;

  // We have grown U as much as possible, so now we form the quotient
  tt := Cputime();
  Anew := New(ParAxlAlg);
  Wnew, psi := quo<W | U>;
  Anew`Wmod := quo<Wmod | [Wmod | Wmod! u : u in Basis(U)] >;
  assert Dimension(Wnew) eq Dimension(Anew`Wmod);
  Anew`W := Wnew;
  Anew`V := V @ psi;
  Anew`fusion_table := A`fusion_table;
  Anew`shape := {@ <{@ i + Dimension(Anew) - Dimension(A) : i in sh[1] @}, sh[2]>
                      : sh in A`shape @};
  Anew`number_of_axes := A`number_of_axes;
  vprintf ParAxlAlg, 4: "Time taken to build modules and vector spaces %o.\n", Cputime(tt);
  
  if Dimension(U) eq Dimension(W) then
    Anew`rels := {@ W | @};
    vprintf ParAxlAlg, 4: "Time taken for ReduceSaturated %o\n", Cputime(t);
    return Anew, psi;
  end if;
  
  tt := Cputime();
  // Build the matrix for psi for use in FastFunction
  psi_mat := Matrix(BaseField(A), Dimension(W), Dimension(Wnew), [W.i@psi : i in [1..Dimension(W)]]);
  
  UpdateAxes(A, ~Anew, psi: matrix := psi_mat);
  vprintf ParAxlAlg, 4: "Time taken to update axes %o\n", Cputime(tt);
  
  tt := Cputime();
  if assigned newalgs then
    UpdateSubalgebras(A, ~Anew, psi: algs := newalgs, maps:=newmaps);
  else
    UpdateSubalgebras(A, ~Anew, psi);
  end if;
  vprintf ParAxlAlg, 4: "Time taken to update subalgebras %o\n", Cputime(tt);
  
  // We calculate the restriction of psi to V so we ensure that the preimage of Vnew lies in V
  tt := Cputime();  
  psi_rest := hom<V->Wnew | [ v@psi : v in Basis(V)]>;

  vprint ParAxlAlg, 2: "  Calculating the new multiplication table.";
  V_new_pullback := [ W | u@@ psi_rest : u in Basis(Anew`V) ];
  
  VV := [Coordinates(V, v) : v in V_new_pullback];
  newmult := BulkMultiply(A`mult, VV, VV);
  prods := FastMatrix([ newmult[i,j] : j in [1..i], i in [1..#VV]], psi_mat);
  
  Anew`mult := [ [ Wnew | ] : i in [1..Dimension(Anew`V)]];
  time for i in [1..Dimension(Anew`V)] do
    for j in [1..i] do
      Anew`mult[i,j] := prods[i*(i-1) div 2 +j];
      Anew`mult[j,i] := Anew`mult[i,j];
    end for;
  end for;
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  
  vprint ParAxlAlg, 2: "  Mapping the remaining relations into the new W.";
  tt := Cputime();
    Anew`rels := {@ v : v in FastMatrix(A`rels, psi_mat) | v ne Wnew!0 @};
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  
  vprintf ParAxlAlg, 4: "Time taken for ReduceSaturated %o\n", Cputime(t);
  return Anew, psi;
end intrinsic;

intrinsic OldReduceSaturated(A::ParAxlAlg, U::ModTupFld) -> ParAxlAlg
  {
  Construct the algebra G-module W/U for a saturated U.
  }
  t := Cputime();
  W := A`W;
  Wmod := A`Wmod;
  V := A`V;

  Anew := New(ParAxlAlg);
  Wnew, psi := quo<W | U>;
  Anew`Wmod := quo<Wmod | [Wmod | Wmod! u : u in Basis(U)] >;
  assert Dimension(Wnew) eq Dimension(Anew`Wmod);
  Anew`W := Wnew;
  Anew`V := V @ psi;
  Anew`fusion_table := A`fusion_table;
  Anew`shape := {@ <{@ i + Dimension(Anew) - Dimension(A) : i in sh[1] @}, sh[2]>
                      : sh in A`shape @};
  Anew`number_of_axes := A`number_of_axes;
  
  if Dimension(U) eq Dimension(W) then
    Anew`rels := {@ W | @};
    return Anew;
  end if;

  Anew`axes := A`axes;
  for i in [1..#A`axes] do
    Anew`axes[i]`id := Anew!((A`axes[i]`id)`elt @ psi);
    Anew`axes[i]`WH := Restriction(Anew`Wmod, Anew`axes[i]`stab);
    
    for attr in {"even", "odd"} do
      for k in Keys(Anew`axes[i]``attr) do
        Anew`axes[i]``attr[k] := sub<Wnew | [ Wnew | w@psi : w in Basis(A`axes[i]``attr[k])] >;
      end for;
    end for;
  end for;

  // Recalculate the subalgebras
  UpdateSubalgebras(A, ~Anew, psi);

  // We calculate the restriction of psi to V so we ensure that the preimage of Vnew lies in V
  
  psi_rest := hom<V->Wnew | [ v@psi : v in Basis(V)]>;

  vprint ParAxlAlg, 2: "  Calculating the new multiplication table.";
  // we use the fact it is symmetric
  vprint ParAxlAlg, 2: "  Calculating the pullback of V.";
  V_new_pullback := [ W | u@@ psi_rest : u in Basis(Anew`V) ];
  vprint ParAxlAlg, 2: "  Calculating half the multiplication table for the new V.";
  Anew`mult := [ [ (A!V_new_pullback[i]*A!V_new_pullback[j])`elt @ psi : j in [1..i] ] : i in [1..Dimension(Anew`V)] ];
  vprint ParAxlAlg, 2: "  Copying the values into the rest of the table using symmetry.";
  for i in [1..Dimension(Anew`V)] do
    for j in [i+1..Dimension(Anew`V)] do
      Anew`mult[i,j] := Anew`mult[j,i];
    end for;
  end for;
  vprint ParAxlAlg, 2: "  Mapping the remaining relations into the new W.";
  Anew`rels := {@ vpsi : v in A`rels | vpsi ne Wnew!0 where vpsi := v@psi @};
  
  vprintf ParAxlAlg, 4: "Time taken for ReduceSaturated %o\n", Cputime(t);
  return Anew;
end intrinsic;
/*

We use the following to impose the relations on the algebra that we have built up to reduce it.

*/
intrinsic ImplementRelations(A::ParAxlAlg: max_number:=#A`rels) -> ParAxlAlg
  {
  Implement the relations we have built up.
  }
  t:=Cputime();
  Anew := A;

  while assigned Anew`rels and #Anew`rels ne 0 do
    vprintf ParAxlAlg, 1: "Dim(A) is %o, Dim(V) is %o, number of relations is %o.\n", Dimension(Anew), Dimension(Anew`V), #Anew`rels;
    U := SaturateSubspace(Anew, sub<Anew`W| Anew`rels[1..Minimum(max_number, #Anew`rels)]>);
    Anew := ReduceSaturated(Anew, U);
  end while;

  vprintf ParAxlAlg, 1: "Dim(A) is %o, Dim(V) is %o.\n", Dimension(Anew), Dimension(Anew`V);
  vprintf ParAxlAlg, 4: "Time taken for ImplementRelations %o\n", Cputime(t);
  return Anew;
end intrinsic;
/*

This is an internal function to impose the eigenvalue condition.

NB add Timesable

*/

intrinsic ImposeEigenvalue(A::ParAxlAlg, i::RngIntElt, lambda::.: implement:=true) -> ParAxlAlg
  {
  Let id be the ith idempotent in W and lambda an eigenvalue.  This imposes the relation u*e - lambda u, for all u in U, where U is the eigenspace associated to lambda.
  }
  W := A`W;
  id := A`axes[i]`id;
  V := A`V;
  if {@ lambda @} in Keys(A`axes[i]`odd) then
    U := A`axes[i]`odd[{@ lambda @}];
  elif {@ lambda @} in Keys(A`axes[i]`even) then
    U := A`axes[i]`even[{@ lambda @}];
  else
    error "The given eigenvalue is not valid.";
  end if;  
  
  A`rels join:= {@ W| w : u in Basis(V meet U) | w ne W!0 where w := (id*A!u)`elt - lambda*u @};

  if implement then
    return ImplementRelations(A);
  else
    return A;
  end if;
end intrinsic;
/*

Implements an inner product for G-modules.

*/
intrinsic GetInnerProduct(W:ModGrp) -> AlgMatElt
  {
  Finds an inner product which is compatible with the G-module structure.
  }
  G := Group(W);
  phi := GModuleAction(W);

  return &+[ Matrix(g*Transpose(g)) where g := h@phi : h in G];
end intrinsic;
/*

Finds complements in G-modules.

*/
intrinsic Complement(W::ModGrp, U::ModGrp: ip:=GetInnerProduct(W)) -> ModGrp
  {
  Finds the complement of U inside W.  Takes an optional argument of a Matrix which is the Gram matrix of an inner product.  This defaults to calculating a G-invariant inner product using GetInnerProduct(W).
  }
  require U subset W: "U is not a submodule of W";
  U_bas := [(W!v) : v in Basis(U)];
  if #U_bas eq 0 then
    return W;
  else
    return sub<W | [W!v : v in Basis(NullSpace(Transpose(Matrix(U_bas)*ip)))]>;
  end if;
end intrinsic;
/*


Decomposes with respect to an inner product correctly! magma only does the standard inner product...

*/
intrinsic DecomposeVectorWithInnerProduct(U::., v::.: ip := GetInnerProduct(Parent(v)), Minv := (Matrix(Basis(U))*ip*Transpose(Matrix(Basis(U))))^-1) -> ., .
  {
  Return the unique u in U and w in the complement of U such that v = u + w.  Defaults to calculating a G-invariant inner product using GetInnerProduct(W).
  }
  require Type(U) in {ModTupFld, ModGrp}: "The space given is not a module or a vector space.";
  W := Parent(v);
  require U subset W: "U is not a submodule of W";
  if Dimension(U) eq 0 then
    return W!0, v;
  end if;
  U_bas := [(W!u) : u in Basis(U)];
  
  vU := v*ip*Transpose(Matrix(U_bas))*Minv*Matrix(U_bas);

  return vU, v-vU;
end intrinsic;

intrinsic DecomposeVectorsWithInnerProduct(U::., L::.: ip := GetInnerProduct(Parent(L[1]))) -> SeqEnum
  {
  For a SetIndx L of vectors v, return a set of tuples <vU, vC> where v = vU + vC is the decomposition into V = U + U^\perp, with respect to an arbitrary inner product.
  }
  require Type(L) in {SeqEnum, SetIndx, List}: "The collection given is not ordered.";
  require Type(U) in {ModTupFld, ModGrp}: "The space given is not a module or a vector space.";
  W := Parent(L[1]);
  require U subset W: "U is not a submodule of W";
  if Dimension(U) eq 0 then
    return [ < W!0, v> : v in L];
  end if;
  U_bas := [(W!v) : v in Basis(U)];
  M := ip*Transpose(Matrix(U_bas))*(Matrix(U_bas)*ip*Transpose(Matrix(U_bas)))^-1*Matrix(U_bas);

  prods := FastMatrix(L, M);

  return [ <prods[i], L[i]-prods[i]> : i in [1..#L]];
end intrinsic;
/*

We wish to expand the space W

We write W = V + C where C is complement.  We then expand to W_new which is:

  S^2(C) + VxC + W

We do the new module in this order this tends to make W be preserved in the quotient when magma quotients out by relations w = x, where x is not in W.

*/
ijpos := function(i,j,n)
  if i le j then
    return &+[ n+1 -k : k in [0..i-1]] -n +j-i;
  else
    return &+[ n+1 -k : k in [0..j-1]] -n +i-j;
  end if;
end function;

intrinsic ExpandSpace(A::ParAxlAlg) -> ParAxlAlg
  {
  Let A = V \oplus C.  This function expands A to S^2(C) \oplus (V \otimes C) \oplus A, with the new V being the old A.  We then factor out by the known multiplications in old V and return the new partial axial algebra.
  }
  t := Cputime();
  require Dimension(A`W) ne Dimension(A`V): "You have already found the multiplication table to build a full algebra - no need to expand!";
  
  vprintf ParAxlAlg, 1: "Expanding space from %o dimensions.\n", Dimension(A);  
  tt := Cputime();
  G := Group(A);
  W := A`W;
  Wmod := A`Wmod;
  ip := GetInnerProduct(Wmod);
  V := A`V;

  // We build the modules and maps
  Vmod := sub<Wmod | [Wmod | v : v in Basis(V)]>;
  Cmod := Complement(Wmod, Vmod: ip:=ip);
  VCmod := TensorProduct(Vmod, Cmod);

  WW, VCmodtoWW, WmodtoWW := DirectSum(VCmod, Wmod);
  C2mod := SymmetricSquare(Cmod);
  Wmodnew, C2modtoWmodnew, WWtoWmodnew := DirectSum(C2mod, WW);
  WmodtoWmodnew := WmodtoWW * WWtoWmodnew;
  VCmodtoWmodnew := VCmodtoWW * WWtoWmodnew;

  // We build the corresponding vector spaces and maps
  Wnew := RSpace(BaseField(A), Dimension(Wmodnew));
  C := RSpaceWithBasis([ W | Wmod!(Cmod.i) : i in [1..Dimension(Cmod)]]);
  VC := RSpace(BaseField(W), Dimension(VCmod));
  C2 := RSpace(BaseField(W), Dimension(C2mod));
  WtoWnew := hom< W -> Wnew | [Wnew | Wmod.i @ WmodtoWmodnew : i in [1..Dimension(Wmod)]]>;
  VCtoWnew := hom< VC -> Wnew | [ Wnew | VCmod.i @ VCmodtoWmodnew : i in [1..Dimension(VCmod)]]>;
  C2toWnew := hom< C2 -> Wnew | [Wnew | C2mod.i @ C2modtoWmodnew : i in [1..Dimension(C2mod)]]>;
  
  Anew := New(ParAxlAlg);
  Anew`Wmod := Wmodnew;
  Anew`W := Wnew;
  Anew`V := W@WtoWnew;
  assert forall{ i : i in [1..Dimension(Wmod)] | Anew`V.i eq W.i @ WtoWnew };
  // We make the assumption that the basis vectors map across correctly
  vprintf ParAxlAlg, 4: "Time taken to build modules and vector spaces %o.\n", Cputime(tt);
  
  Anew`shape := {@ <{@ i + Dimension(Anew) - Dimension(A) : i in sh[1] @}, sh[2]>
                      : sh in A`shape @};
  Anew`number_of_axes := A`number_of_axes;
  Anew`fusion_table := A`fusion_table;
  Anew`rels := {@ Wnew | @};

  vprint ParAxlAlg, 2: "  Building the multiplication.";
  tt := Cputime();
  // begin by building the multiplication
  Anew`mult := [[Wnew | ] : i in [1..Dimension(Anew`V)]];
  // We precompute the decompositions
  decomp := DecomposeVectorsWithInnerProduct(V, Basis(W): ip:=ip);
  // we transform them into vectors in their natural spaces
  dimV := Dimension(V);
  dimC := Dimension(C);
  decompV := [ Coordinates(V,t[1]) : t in decomp ];
  decompC := [ Coordinates(C,t[2]) : t in decomp ];
  
  // precompute all the products we require
  // First build the matrix for WtoWnew as we will need it later also
  WtoWnew_mat := Matrix(BaseField(A), Dimension(W), Dimension(Wnew), [W.i@WtoWnew : i in [1..Dimension(W)]]);
  
  prodsV := FastMatrix(BulkMultiply(A, decompV), WtoWnew_mat);
  
  /*
  prods := FastMatrix([ A`mult[i,j], j in [1..i], i in [1..dimV]], WtoWnew_mat);
  newmult := [ [ Wnew | prods[ZZ!(i*(i-1)/2+j)] : j in [1..i] ] : i in [1..dimV]];
  for i in [1..dimV] do
    for j in [1..i-1] do
      newmult[j][i] := newmult[i][j];
    end for;
  end for;
  prodsV2 := BulkMultiply(newmult, [decomp[i,1] : i in [1..#decomp]], [decomp[i,1] : i in [1..#decomp]]);
  */
  
  // Speed up using change of basis
  VCmult := [ [Wnew.(Dimension(C2)+dimC*(i-1)+j) : j in [1..dimC]]: i in [1..dimV]];
  newVCmult := BulkMultiply(VCmult, decompV, decompC);
  
  if dimV eq 0 or dimC eq 0 then
    prodsVC := [ Wnew!0 : i in [1..(#decomp*(#decomp+1) div 2)]];
  else
    prodsVC := [ newVCmult[i,j] + newVCmult[j,i] : j in [1..i], i in [1..#decomp]];
  end if;

  C2mult := [ [Wnew.ijpos(i,j,dimC) : j in [1..dimC]]: i in [1..dimC]];
  prodsC2 := BulkMultiply(C2mult, decompC, decompC);

  Anew`mult := [[Wnew | ] : i in [1..Dimension(W)]];

  for i in [1..Dimension(W)] do
    for j in [1..i] do
      Anew`mult[i][j] := prodsV[i*(i-1) div 2 +j] + prodsVC[i*(i-1) div 2+j] + prodsC2[i,j];
      if j ne i then
        Anew`mult[j][i] := Anew`mult[i][j];
      end if;
    end for;
  end for;
  vprintf ParAxlAlg, 4: "  Time taken to build the multiplication table %o.\n", Cputime(tt);

  // We now build the axes
  vprint ParAxlAlg, 2: "  Updating the axes.";
  tt := Cputime();
  UpdateAxes(A, ~Anew, WtoWnew: matrix:=WtoWnew_mat);
  vprintf ParAxlAlg, 4: "  Time taken for updating the axes %o.\n", Cputime(tt);

  // We update the subalgs
  vprint ParAxlAlg, 2: "  Updating the subalgebras.";
  tt := Cputime();
  subalgs := New(SubAlg);
  subalgs`subsps := {@ Parent(Wnew) | @};
  subalgs`maps := [* *];
  subalgs`algs := A`subalgs`algs;
  for i in [1..#A`subalgs`subsps] do
    subsp := A`subalgs`subsps[i];
    map, homg, pos := Explode(A`subalgs`maps[i]);
    alg := A`subalgs`algs[pos];
    
    subspV := subsp meet V;
    bas := ExtendBasis(subspV, subsp);
    basV := bas[1..Dimension(subspV)];
    basC := bas[Dimension(subspV)+1..Dimension(subsp)];
    
    // We also calculate their images in Wnew
    basnew := FastMatrix(bas, WtoWnew_mat);
    basnewV := basnew[1..Dimension(subspV)];
    basnewC := basnew[Dimension(subspV)+1..Dimension(subsp)];
    
    vprint ParAxlAlg, 4: "  Calculating products";
    time prodsVC := [[ Wnew |(Anew!v * Anew!u)`elt : v in basnewV] : u in basnewC];
    time prodsVC2 := BulkMultiply(Anew, basnewV, basnewC);
    assert prodsVC eq prodsVC2;
    
    time prodsC2 := [[ Wnew |(Anew!basnewC[k] * Anew!basnewC[l])`elt : k in [1..l]] : l in [1..#basC]];
    time prodsC22 := BulkMultiply(Anew, basnewC);
    assert prodsC22 eq &cat prodsC2;

    vprint ParAxlAlg, 4: "  Updating subspaces and maps";    
    newsubsp := subsp@WtoWnew + sub< Wnew | &cat prodsVC cat &cat prodsC2>;
    
    newmap := hom<newsubsp -> alg`W | [<basnew[i], bas[i]@map> : i in [1..#bas]] cat
       [ <prodsVC[l,k], (alg!basV[k]@map * alg!basC[l]@map)`elt> : k in [1..#basV], l in [1..#basC]] cat [ <prodsC2[l,k], (alg!basC[k]@map * alg!basC[l]@map)`elt> : k in [1..l], l in [1..#basC]]>;
       
    Include(~subalgs`subsps, newsubsp);
    Append(~subalgs`maps, <newmap, homg, pos>);
    
    // If we have updated our map, we want to pull back the eigenvectors.
    if #basC ne 0 then
      vprint ParAxlAlg, 4: "  Using updated map to gather new eigenvectors and relations.";
      Im_sp := Image(newmap);
      Gact := GModuleAction(Anew`Wmod);
      // NB Im_sp is a H-submodule of alg, where H = Group(alg).  If an axis id of A is conjugate to an axis of alg by g, then the double coset KgH, where K = Stab(id) are all the elements which conjugate id to an axis of alg (of a given type). There could be additional outer automorphisms of alg indiuced by G, but we would see these in A and they would just fuse classes of axes in alg.  So, we need only find a single g to conjugate the eigenspaces.

      // We precompute the orbits of the axes
      // It is much faster applying group elements in A than Anew
      if not assigned axis_orbs then
        vprint ParAxlAlg, 4: "  Precompute the orbit of each axis.";
        ttt := Cputime();
        trans := [];
        orbs := [];
        for j in [1..#Anew`axes] do
          trans[j] := Transversal(G, A`axes[j]`stab);
          orbs[j] := [ (A`axes[j]`id*g)`elt : g in trans[j]];
        end for;
        images := FastMatrix(&cat orbs, WtoWnew_mat);
        count := 0;
        axis_orbs := [];
        for j in [1..#trans] do
          axis_orbs[j] := images[count+1..count+#trans[j]];
          count +:= #trans[j];
        end for;
        vprintf ParAxlAlg, 4: "  Time taken %o.\n", Cputime(ttt);
      end if;
      
      print "Calculating S";
      time S := {@ <j,k,g> : j in [1..#Anew`axes], k in [1..#alg`axes] | 
              exists(g){trans[j,l] : l in [1..#trans[j]] | axis_orbs[j,l] in newsubsp and axis_orbs[j,l]@newmap eq alg`axes[k]`id`elt }@};
      
      // Precompute the pullback matrix from Im_sp to Wnew
      time pullback_mat := Matrix([Im_sp.l@@newmap : l in [1..Dimension(Im_sp)]]);
      
      for s in S do
        j,k,g := Explode(s);
        
        // gather together all the eigenvectors needed and precompute the maps required
        ttt := Cputime();
        dims := CheckEigenspaceDimensions(alg : U := Im_sp)[k];
        allkeys := AssociativeArray();
        allkeys["even"] := [{@ @}, {@ 1 @}, {@ 0 @}, {@ 1/4 @}, {@ 1, 0 @}, {@ 1, 1/4 @}, {@ 0, 1/4 @}, {@ 1, 0, 1/4 @}];
        allkeys["odd"] := [{@ 1/32 @}];

        eigvects := &cat[ Basis(alg`axes[k]``attr[key] meet Im_sp) : key in allkeys[attr], attr in ["even", "odd"]];
        eigvects := [ Coordinates(Im_sp, v) : v in eigvects];
        
        // We need to pullback, apply g^-1
        time M := pullback_mat * ((g^-1)@Gact);
        time newvects := FastMatrix(eigvects, M);
        vprintf ParAxlAlg, 4: "Completed precomputations in %o\n", Cputime(ttt);

        offset := 0;
        for attr in {@"even", "odd"@} do
          for key in allkeys[attr] do
            Anew`axes[j]``attr[key] +:=  sub<Wnew | newvects[offset+1.. offset+Dimension(alg`axes[k]``attr[key] meet Im_sp)]>;
            offset +:= Dimension(alg`axes[k]``attr[key] meet Im_sp);
          end for;
        end for;
      end for;
      // Also collect the relations coming from the multiplication in the subalgs
      Anew`rels join:= {@ Wnew | u : u in Basis(Kernel(newmap))@};
    end if;
  end for;
  Anew`subalgs := subalgs;
  vprintf ParAxlAlg, 4: "  Time taken for updating the subalgebras %o\n", Cputime(tt);

  // We also collect some relations coming from the eigenvectors
  vprint ParAxlAlg, 2: "  Collecting any new eigenvalue relations.";
  tt := Cputime();
  for i in [1..#A`axes] do
    for lambda in Anew`fusion_table`eigenvalues do // could skip 1
      Anew := ImposeEigenvalue(Anew, i, lambda: implement:=false);
    end for;
  end for;
  vprintf ParAxlAlg, 4: "Time taken %o.\n", Cputime(tt);

  vprintf ParAxlAlg, 4: "Total time taken for ExpandSpace (before ImplementRelations) %o\n", Cputime(t);
  Anew := ImplementRelations(Anew);
  vprintf ParAxlAlg, 4: "Total time taken for ExpandSpace (including ImplementRelations) %o\n", Cputime(t);
  return Anew;
end intrinsic;
/*

This just finds the odd and even parts acording to the grading.

*/
intrinsic ForceGrading(A::ParAxlAlg) -> ParAxlAlg
  {
  Let inv be a Miyamoto involution corresponding to an idempotent e.  The action of inv on W has two eigenspaces, positive and negative, which gives the grading of the action of the idempotent e.  For each idempotent e, we find the grading and store these.
  }
  actionhom := GModuleAction(A`Wmod);
  for i in [1..#A`axes] do
    inv := A`axes[i]`inv;
    inv_mat := inv @ actionhom;

    A`axes[i]`odd[&join Keys(A`axes[i]`odd)] := Eigenspace(inv_mat, -1);
    A`axes[i]`even[&join Keys(A`axes[i]`even)] := Eigenspace(inv_mat, 1);
  end for;
  return A;
end intrinsic;
/*

This forces the grading and mods out by any relations coming from the odd part

*/
intrinsic ExpandOdd(A::ParAxlAlg) -> ParAxlAlg
  {
  Forces the grading and then implements the relations coming from the eigenvalues in the odd part.
  }
  vprint ParAxlAlg, 1: "Forcing the grading and imposing the odd relations.";
  t := Cputime();
  A := ForceGrading(A);

  for i in [1..#A`axes] do
    for k in [k[1] : k in Keys(A`axes[i]`odd) | #k eq 1] do
      A := ImposeEigenvalue(A, i, k: implement := false);
    end for;
  end for;

  Anew := ImplementRelations(A);
  vprintf ParAxlAlg, 4: "Time taken for odd routine %o\n", Cputime(t);
  return Anew;
end intrinsic;
/*

We expand the even part.

*/
//-------------------------------
// We list some internal functions which we will use to reduce the even part
intrinsic MultiplyDown(A::ParAxlAlg, keys::SeqEnum, i::RngIntElt) -> ParAxlAlg
  {
  Let A_S denote the sum of eigenspaces. For lambda in S the elements id*u - lambda*u are all in A_\{S - lambda\}, where id is the idempotent.
  }
  t := Cputime();
  orig := CheckEigenspaceDimensions(A: empty := true);
  vprint ParAxlAlg, 2: "  Multiplying down using eigenvalues.";
    
  V := A`V;
  id := Coordinates(V, A`axes[i]`id`elt);
  id_mat := &+[ Matrix( [id[i]*A`mult[j,i] : j in [1..Dimension(V)]]) : i in [1..Dimension(V)] | id[i] ne 0];
  
  for k in Reverse(keys) do
    U := A`axes[i]`even[k] meet A`V;
    for lambda in k do
      prods := FastMatrix([ Coordinates(V,u) : u in Basis(U)], id_mat);
      A`axes[i]`even[k diff {@ lambda @}] +:= 
           sub<A`W | {@ w : j in [1..Dimension(U)] | w ne A`W!0 
                      where w := prods[j] - lambda*U.j @}>;
    end for;
  end for;
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(t);
  vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
  return A;
end intrinsic;

intrinsic SumUpwards(A::ParAxlAlg, keys::SeqEnum, i::RngIntElt) -> ParAxlAlg
  {
  For the ith axis we do the following on the even subspaces
   A_\{S+T\} += A_\{S+T\} + A_S + A_T
  }
  tt := Cputime();
  orig := CheckEigenspaceDimensions(A: empty := true);

  // build a sequence of keys by key length
  len := Max([#k : k in keys]);
  keylen := [[ k : k in keys | #k eq j] : j in [0..len]];
  
  vprint ParAxlAlg, 2: "  Summing upwards.";
  for j in [2..#keylen] do
    for key in keylen[j] do
      A`axes[i]`even[key] +:= &+[ A`axes[i]`even[k] : k in keylen[j-1] | k subset key];
    end for;
  end for;
  
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
  return A;
end intrinsic;

intrinsic IntersectionDown(A::ParAxlAlg, keys::SeqEnum, i::RngIntElt) -> ParAxlAlg
  {
  For the ith axis we take intersections on the even subspaces:
  A_\{S \cap T\} += A_S \cap A_T
  }
  tt := Cputime();
  orig := CheckEigenspaceDimensions(A: empty := true);
  
  // build a sequence of keys by key length without the largest one
  len := Max([#k : k in keys]);
  keylen := [[ k : k in keys | #k eq j] : j in [0..len-1]];
  
  vprint ParAxlAlg, 2: "  Intersecting downwards.";
  
  for j in Reverse([1..#keylen-1]) do
    for key in keylen[j] do
      ints := { {@k,l@} : k,l in &cat keylen[j+1..#keylen] | k meet l eq key};
      A`axes[i]`even[key] +:= &+ [ A`axes[i]`even[tup[1]] meet A`axes[i]`even[tup[2]] : tup in ints];
    end for;
  end for;
  
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
  return A;
end intrinsic;

intrinsic ApplyUsefulFusionRules(A::ParAxlAlg, i::RngIntElt) -> ParAxlAlg
  {
  We impose the useful fusion rules to grow the subspaces for the ith axis.
  }
  tt := Cputime();
  orig := CheckEigenspaceDimensions(A: empty := true);
  vprint ParAxlAlg, 2: "  Applying useful fusion rules.";
  for tup in UsefulFusionRules(A`fusion_table) do
    A`axes[i]`even[tup[3]] +:= sub< A`W | &cat BulkMultiply(A, Basis(A`axes[i]`even[tup[1]] meet A`V), Basis(A`axes[i]`even[tup[2]] meet A`V))>;
  end for;
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
  return A;
end intrinsic;

intrinsic ApplyGroupTrick(A::ParAxlAlg, i::RngIntElt) -> ParAxlAlg
  {
  If w in A_S where 1 in S, then w*h-w in A_\{S -1 \}, where h is in the stabiliser of the corresponding axis.  This routine applies this trick to the largest even subspace for the ith axis.  (The result will be propogated down by taking intersections.)
  }
  tt := Cputime();
  orig := CheckEigenspaceDimensions(A: empty := true);
  W := A`W;
  Hmat := [ h - IdentityMatrix(BaseField(A), Dimension(A)) : h in MatrixGroup(A`axes[i]`WH)];
  
  keys := Keys(A`axes[i]`even);
  max_size := Max([#S : S in keys]);
  assert exists(S){S : S in keys | #S eq max_size};
  vprint ParAxlAlg, 2: "  Applying w*h-w trick.";
  
  prods := [ FastMatrix({@ w : w in Basis(A`axes[i]`even[S])@}, h) : h in Hmat];
  A`axes[i]`even[S diff {@1@}] +:= sub< W | &join prods >;
  vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
  vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
  return A;
end intrinsic;
//------------------------------------------
/*

We write a function to apply some of the above tricks in a good order

*/

/*

This function returns the a SeqEnum of dimensions of the subspaces for a given axis i.
We adjust by subtracting the dim of the empty subspace.

*/
StageDimensions := function(A, i)
  dim := CheckEigenspaceDimensions(A:empty:=true)[i];
  dim0 := dim[1];
  return Remove([ d - dim0 : d in dim], 1);
end function;

intrinsic Cheap_work(A::ParAxlAlg, keys, i) -> ParAxlAlg
  {
  A collection of functions which are cheap to apply reduce the even part.  Consists of MultiplyDown, SumUpwards and IntersectionDown.
  }
  stage_flag := [ [] : i in [1..3]];
  while true do
    so := exists(j){j : j in [1..3] | StageDimensions(A,i) ne stage_flag[j]};
    if not so then
      break;
    elif j eq 1 then
      A := MultiplyDown(A, keys, i);
    elif j eq 2 then
      A := SumUpwards(A, keys, i);
    elif j eq 3 then
      A := IntersectionDown(A, keys, i);
    end if;
    stage_flag[j] := StageDimensions(A, i);
  end while;
  return A;  
end intrinsic;
/*

A short procedure for updating the empty eigenspaces

*/
PropogateRels := procedure(~A, j)
  U := A`axes[j]`even[{@@}];
  for i in [ i : i in [1..#A`axes] | i ne j] do
    A`axes[i]`even[{@@}] +:= U;
  end for;
end procedure;

intrinsic ExpandEven(A::ParAxlAlg: reduction_limit := Maximum(Floor(Dimension(A)/4), 50)) -> ParAxlAlg
  {
  We repetedly apply the reduction tricks until there is no further change.  We reduce the algebra if the dimension of the space we can mod out by is at least the reduction_limit.
  }
  t := Cputime();
  vprint ParAxlAlg, 1: "Imposing the even relations.";
  
  keys := Setseq(Keys(A`axes[1]`even));
  Sort(~keys, func<x,y| #x-#y>);
  
  // We have an algorithm which we organise into several stages.  Higher stages are more computationally expensive than the previous stages, so we wish to do all stages on all axes until they don't change anymore before moving on to the next stage.
  // We complete a stage and then retry the previous stages to see if these will now give further progress.  We then go on to a higher stage.
  
  // We define a flag of the dimension of all subspaces after a given stage on a given axis.
  // In this way we keep track of whether there has been any change since the previous time we applied that stage and so if it is worth doing that stage again.
  stage_flag := [[ [] : i in [1..4]] : i in [1..#A`axes]];
  
  // We only wish to do the wh-w trick once per ExpandSubspace, so we create a flag for this
  wh_trick_flag := [ false : i in [1..#A`axes]];
  
  while true do
  
    // We find the lowest stage so that there is an axis which has changed since we last worked on it.
    so := exists(tup){ <i, j> : i in [1..#A`axes], j in [1..4] |
                           stage_flag[i,j] ne StageDimensions(A, i)};
    if so then
      // There is work to do, so we do it!
      i, stage := Explode(tup);

      // We begin by doing the cheap work
      if stage eq 1 then
        A := Cheap_work(A, keys, i);
        PropogateRels(~A, i);
        stage_flag[i, stage] := StageDimensions(A, i);
      
      // We apply the useful fusion rules
      elif stage eq 2 then
        A := ApplyUsefulFusionRules(A, i);
        PropogateRels(~A, i);
        stage_flag[i, stage] := StageDimensions(A, i);
        
      // We make the intersections stabiliser-invariant
      elif stage eq 3 then
        tt := Cputime();
        vprint ParAxlAlg, 2: "  Making the subspaces stabiliser-invariant.";
        orig := CheckEigenspaceDimensions(A: empty := true);
        // The whole even space is already H-invariant
        for k in Remove(keys, #keys) do
          if k eq {@@} then
            module := A`Wmod;
          else
            module := A`axes[i]`WH;
          end if;
          A`axes[i]`even[k] := GInvariantSubspace(module, A`W, Basis(A`axes[i]`even[k]));
        end for;
        PropogateRels(~A, i);
        stage_flag[i, stage] := StageDimensions(A, i);
        vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
        vprintf ParAxlAlg, 3: "Dimension of subspaces before and after are \n     %o\n and %o. \n", orig[i], CheckEigenspaceDimensions(A: empty := true)[i];
        
      // We apply the w*h-w trick
      elif stage eq 4 then
        // We only want to apply it once per expansion step
        if not wh_trick_flag[i] then
          wh_trick_flag[i] := true;
          A := ApplyGroupTrick(A, i);
          // No need to propagate as it only adds to the {0, 1/4} eigenspace
        end if;
        stage_flag[i, stage] := StageDimensions(A, i);
      end if;
    end if;
    
    // if there is no work to do, or we have found enough relations, then we mod out and check to see if we are really done.
    if not so or Dimension(A`axes[1]`even[{@@}]) ge reduction_limit then
      A`rels join:= {@ A`W | w : w in Basis(A`axes[1]`even[{@@}]) @};
      if #A`rels eq 0 then
        // There are no relations to mod out by, so we must be done.
        vprintf ParAxlAlg, 1: "\nDim(A) is %o, Dim(V) is %o.\n", Dimension(A), Dimension(A`V);
        vprintf ParAxlAlg, 4: "Time taken for even routine %o\n", Cputime(t);
        return A;
      else
        A := ImplementRelations(A);
      end if;
    end if;
    
    // We could be done already, so we check
    if Dimension(A) eq 0 or (Dimension(A) eq Dimension(A`V) and
      forall{i : i in [1..#A`axes] | &+[Dimension(A`axes[i]`even[k]) : k in keys | #k eq 1]
        + &+[Dimension(A`axes[i]`odd[k]) : k in Keys(A`axes[i]`odd) | #k eq 1]
            eq Dimension(A)})
          then

      vprintf ParAxlAlg, 1: "\nDim(A) is %o, Dim(V) is %o.\n", Dimension(A), Dimension(A`V);
      vprintf ParAxlAlg, 4: "Time taken for even routine %o\n", Cputime(t);
      return A;
    end if;
  end while;

end intrinsic;

intrinsic OldExpandEven(A::ParAxlAlg: reduction_limit := 50) -> ParAxlAlg
  {
  We repetedly apply the reduction tricks until there is no further change.  We reduce the algebra if the dimension of the space we can mod out by is at least the reduction_limit.
  }
  t := Cputime();
  vprint ParAxlAlg, 1: "Imposing the even relations.";
  
  axes_to_reduce := [1..#A`axes];
  wh_trick_flag := [ false : i in [1..#A`axes]];
  dims := [];
  
  // We continue to try to reduce until there is no more reduction
  while CheckEigenspaceDimensions(A) ne dims do
    dims := CheckEigenspaceDimensions(A);
    
    // We do work on each axis in turn as work gets harder on each axis the more work is done on it, so we want to do all the easy work first in the hope that we can then reduce the algebra and work on a smaller one instead.
    for i in axes_to_reduce do
      vprintf ParAxlAlg, 2: "Processing for axis number %o\n", i;
      vprintf ParAxlAlg, 3: "Dimension of all subspaces are %o. \n", CheckEigenspaceDimensions(A: empty := true);
      
      keys := Setseq(Keys(A`axes[i]`even));
      Sort(~keys, func<x,y| #x-#y>);
      
      // We begin by doing the cheap work
      A := Cheap_work(A, keys, i);
    
      // We apply the useful fusion rules
      A := ApplyUsefulFusionRules(A, i);
      A := Cheap_work(A, keys, i);
      if Dimension(A`axes[i]`even[{@@}]) ge reduction_limit then
        A`rels join:= {@ A`W | w : w in Basis(A`axes[i]`even[{@@}]) @};
        A := ImplementRelations(A);
        if Dimension(A`V) eq Dimension(A) then
          // *** Nedd to fix***
          // we need to first do some remaining reduction on the subspaces so they are completed.
          return A;
        end if;
        axes_to_reduce := [1..#A`axes];
        wh_trick_flag := [ false : i in [1..#A`axes]];
      end if;
      
      // We make the intersections stabiliser-invariant
      tt := Cputime();
      vprint ParAxlAlg, 2: "  Making the subspaces stabiliser-invariant.";
      for k in keys do
        A`axes[i]`even[k] := GInvariantSubspace(A`axes[i]`WH, A`W, Basis(A`axes[i]`even[k]));
      end for;
      vprintf ParAxlAlg, 4: "  Time taken %o\n", Cputime(tt);
      A := Cheap_work(A, keys, i);
      if Dimension(A`axes[i]`even[{@@}]) ge reduction_limit then
        A`rels join:= {@ A`W | w : w in Basis(A`axes[i]`even[{@@}]) @};
        A := ImplementRelations(A);
        if Dimension(A`V) eq Dimension(A) then
          return A;
        end if;
        axes_to_reduce := [1..#A`axes];
        wh_trick_flag := [ false : i in [1..#A`axes]];
      end if;

      // We apply the w*h-w trick
      if not wh_trick_flag[i] then
        wh_trick_flag[i] := true;
        A := ApplyGroupTrick(A, i);
        A := Cheap_work(A, keys, i);
        if Dimension(A`axes[i]`even[{@@}]) ge reduction_limit then
          A`rels join:= {@ A`W | w : w in Basis(A`axes[i]`even[{@@}]) @};
          A := ImplementRelations(A);
          if Dimension(A`V) eq Dimension(A) then
            return A;
          end if;
          axes_to_reduce := [1..#A`axes];
          wh_trick_flag := [ false : i in [1..#A`axes]];
        end if;
      end if;

      // We don't want to continue to work on an axis that we have no further change in
      if CheckEigenspaceDimensions(A)[i] eq dims[i] then
        Remove(~axes_to_reduce, Position(axes_to_reduce, i));
      end if;
  
      // we add the relations we have found to rels
      A`rels join:= {@ A`W | w : w in Basis(GInvariantSubspace(A`Wmod, A`W, Basis(A`axes[i]`even[{@@}]))) @};
      // We can use the relations already found in the next stage
      for j in [1..#A`axes] do
        A`axes[j]`even[{@@}] +:= sub<A`W | A`rels>;
      end for;
    end for;
  end while;

  vprintf ParAxlAlg, 4: "Time taken for even routine %o\n", Cputime(t);
  return ImplementRelations(A);
end intrinsic;
