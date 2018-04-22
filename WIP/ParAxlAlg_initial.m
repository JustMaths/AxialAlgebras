/*

Functions for creating an initial object

*/
QQ := Rationals();

Subalgs_sort := function(x,y)
  if #y[3] ne #x[3] then
    return #y[3] - #x[3];
  elif x[1] ne y[1] then
    return x[1]-y[1];
  else
    return x[2]-y[2];
  end if;
end function;
/*

A function for sorting the shapes

*/
ShapeSort := func<x,y | x[1] gt y[1] select -1 else x[1] lt y[1] select 1 else x[2] gt y[2] select 1 else x[2] lt y[2] select -1 else 0>;
/*

function for sorting eigenvalues in the order 1, 0, everything else

*/
function EigenvalueSort(x,y)
  if x eq 1 then
    return -1;
  elif y eq 1 then
    return 1;
  elif x eq 0 then
    return -1;
  elif y eq 0 then
    return 1;
  else
    return x-y;
  end if;
end function;
/*

Given a permutation group, determines all the shapes of Axial algebras which are possible where we assume the axes are in bijection with a union of conjugacy classes

*/
intrinsic Shapes(G::GrpPerm) -> SeqEnum
  {
  Returns the shapes which coorespond to the action of G on a union of conjugacy classes of involutions.
  }
  all_shapes := [];
  Axs := InvolutionGSets(G);
  for Ax in Axs do
    taus := AdmissibleTauMaps(Ax);
    for tauset in taus do
      tau, stab := Explode(tauset);
      all_shapes cat:= Shapes(Ax, tau, stab);
    end for;
  end for;

  return all_shapes;
end intrinsic;
/*

Returns the GSets which are got in the old way.

*/
intrinsic InvolutionGSets(G::GrpPerm) -> SeqEnum
  {
  Returns a sequence of GSets which correspond to the action of G on a union of conjugacy classes of involutions.  We dedupe this for the action of the outer automorphism group of G.
  }
  class2 := {@ c[3] : c in Classes(G) | c[1] eq 2 @};

  orbs := {@ Orbit(G,x) : x in class2 @};
  // Two sets of involutions which are conjugate under an outer automorphism will produce the same posibilities for the shape.
 
  aut := AutomorphismGroup(G);
  autFP, FPmap := FPGroup(aut);
  out, out_map := OuterFPGroup(aut);
  outPerm, perm_map := PermutationGroup(out);

  elts_out := [ g@@perm_map@@out_map@FPmap : g in outPerm ];
  
  // We need to dedupe the set of all possible subsets of orbs for those which are conjugate under the outer automorphisms
  // At the same time, we check for generation of G
  
  all_invs := {@ @};
  for invs in {@ IndexedSet(x) : x in Subsets(Set(orbs)) | x ne {} @} do
    if sub<G | &join invs > ne G then
      continue;
    end if;
    if not exists(t){ f : f in elts_out | {@ GSet(G, o@f) : o in invs @} in all_invs } then
      Include(~all_invs, invs);
    end if;
  end for;

  all_GSets := [];
  for invs in all_invs do
    idems := &join invs;

    Ax := IndexedSet([1..#idems]);
    tau := map<Ax -> G | i :-> idems[i]>;
    AxxG := CartesianProduct(Ax, G);
    f := map< AxxG -> Ax | y :-> Position(idems,((y[1] @ tau)^y[2]))>;
    Ax := GSet(G, Ax, f);
    if IsTrivial(ActionKernel(G,Ax)) then
      Include(~all_GSets, Ax);
    end if;
  end for;
  
  return Sort(all_GSets, func< x,y| #x-#y>);
end intrinsic;
/*

Given a GSet Ax, returns the admissible tau maps together with their stabilisers.

*/
intrinsic AdmissibleTauMaps(Ax::GSet) -> SeqEnum
  {
  Given a GSet Ax, we find all the admissible tau maps up to automorphisms of the action.
  }
  G := Group(Ax);
  orbs := Orbits(G, Ax);

  orb_reps := [Representative(o) : o in orbs];
  possibles := [ #orbs[i] eq 1 select {@ Identity(G) @} 
        else {@ g : g in Centre(Stabiliser(G, Ax, orb_reps[i])) | Order(g) eq 2 @}
                   : i in [1..#orbs ]];
  
  cart := [ c : c in CartesianProduct(possibles)];
  
  tau_maps := {@ @};
  pairs_orbs := Orbits(G, GSet(G,Ax,{ {@i,j@} : j in [i+1..#Ax], i in [1..#Ax]}));
  pairs_orb_reps := [ Representative(o) : o in pairs_orbs];
  
  for poss in CartesianProduct(possibles) do
    def := &cat[ [ <j,poss[i]^g> where _,g := IsConjugate(G, Ax, orb_reps[i], j) : j in orbs[i]] : i in [1..#orbs]];
    Sort(~def, func<x,y|x[1]-y[1]>);
    def := [def[i,2] : i in [1..#def]];
    tau := map< Ax -> G | i:-> def[i]>;
  
    // We verify it is admissible
    for pair in pairs_orb_reps do
      D := sub<G | pair[1]@tau, pair[2]@tau>;
      o1 := Orbit(D, Ax, pair[1]);
      o2 := Orbit(D, Ax, pair[2]);
      if #o1 ne #o2 then
        continue poss;
      elif o1 eq o2 then
        if #o1 notin {3,5} then
          continue poss;
        end if;
      else
        if #o1 notin {1,2,3} then
          continue poss;
        end if;
      end if;
    end for;

    if sub<G | Image(tau)> ne G then
      continue poss;
    end if;
    
    Include(~tau_maps, tau);
  end for;
  
  if #tau_maps eq 0 then
    return [];
  end if;
  
  // We now wish to dedupe the set of tau maps using the automorphisms of Ax
  
  phi, GG := Action(G, Ax);
  GAx := Stabiliser(Sym(#Ax), Set(orbs));
  N := Normaliser(GAx, GG);
  // N is the automorphism group of the action of G on Ax
  
  // We must define equality of maps
  
  MapEq := function(f,g)
    return forall{i: i in orb_reps | i@f eq i@g};
  end function;
  
  tau_return := function(f)
    assert exists(g){g : g in tau_maps | MapEq(f,g)};
    return g;
  end function;
  
  // The action on tau maps is
  // tau_n := tau(i^(n^-1))^n
  
  tausxN := CartesianProduct(tau_maps, N);
  f := map< tausxN -> tau_maps | y :-> tau_return(map<Ax-> G | i:-> ((((i^(y[2]^-1))@y[1])@phi)^y[2])@@phi >) >;
  Taus := GSet(N, tau_maps, f);
  
  return [ <tau, Stabiliser(N, Taus, tau)> : tau in [ o[1] : o in Orbits(N, Taus)]];
end intrinsic;
/*

Given a GSet Ax and an admissible tau map, return the shapes of possible algebras, deduped by the action of stab.

*/
FindMinRep := function(orb, L, num)
  assert exists(l){ l : l in L | exists{ o : o in orb | o[1] eq l}};
  lorb := {@ x : x in orb | x[1] eq l @};
  assert exists(pair){ x : i in L cat [ i : i in [1..num] | i notin L] |
                     exists(x){x : x in lorb | x[2] eq i}};
  return pair;
end function;

intrinsic Shapes(Ax::GSet, tau::Map, stab::GrpPerm) -> SeqEnum
  {
  Given a GSet Ax and a tau map, we find all the possible shapes of algebra.
  }
  G := Group(Ax);
  
  orbs := Orbits(G, Ax);
  orb_reps := [o[1] : o in orbs];
  // We find the orbit representatives on pairs and so the possible 2-gen subalgebras
  pairs_orb_reps := [ FindMinRep(o, orb_reps, #Ax) : o in Orbits(ActionImage(G, GSet(G,Ax,{ {@i,j@} : j in [i+1..#Ax], i in [1..#Ax]})))];

  subalgs := Setseq({ <o[1],o[2],Orbit(D,Ax,o[1]) join Orbit(D,Ax,o[2])>  where D := sub<G | o[1]@tau, o[2]@tau> : o in pairs_orb_reps });
  Sort(~subalgs, Subalgs_sort);  // This sorts them in size order, largest first

  // We do not get free choice over all the 2-gen subalgebras.  Some are contained in some others.
  // Formally, there is a graph with vertices being the subalgs and edges given by domination, where one subalgebra is contained in another.  We find the connected components.

  defining_shapes := [];
  for t in subalgs do
    involved := [ i : i in [1..#defining_shapes] | 
          exists{ sh : sh in defining_shapes[i] |
          exists{ j : j in [1..#sh[2]] |
               t[3] subset sh[2,j] or sh[2,j] subset t[3] }}];
    if #involved eq 0 then
      Append(~defining_shapes, {@ < t, {@ Image(g,Ax,t[3]) : g in G @} > @});
    else
      // We must merge all the shapes which are involved with the new one.
      defining_shapes[involved[1]] join:= IndexedSet(&join {@ defining_shapes[i] : i in involved[2..#involved] @}) join {@ < t, {@ Image(g,Ax,t[3]) : g in G @} > @};
      for i in Reverse(involved)[1..#involved-1] do
        Remove(~defining_shapes, i);
      end for;
    end if;
  end for;

  defining_shapes := [ Sort({@ t[1] : t in sets @}, Subalgs_sort) : sets in defining_shapes ];

  // Now we need to pick the possible choices for each connected component

  // If the subalgebra has 5, or 6 axes, there is no choice and it is 5A, or 6A
  shape := [];
  while #defining_shapes ne 0 and #defining_shapes[1,1,3] ge 5 do
    for o in defining_shapes[1] do
      if #o[3] eq 6 then 
        Append(~shape, [* o[1], o[2], "6A" *]);
      elif #o[3] eq 5 then
        Append(~shape, [* o[1], o[2], "5A" *]);
      end if;
    end for;
    Remove(~defining_shapes, 1);
  end while;

  // Check whether there are any subalgebras left to define.
  if #defining_shapes eq 0 then
    return [ [*Ax, tau, shape*] ];
  end if;

  // There is choice over the remaining subalgebras: these are either length 2, 3, or 4
  // There are two choices for each

  // We wish to define an action of stab on the remaining defining_shapes
  def_shapes_orbs := [ &join { Orbit(G, Ax, {t[1], t[2]}): t in set} : set in defining_shapes];

  EltInOrb := function(x)
    assert exists(i){ i : i in [1..#def_shapes_orbs] | x in def_shapes_orbs[i]};
    return i;
  end function;

  num_shapes := IndexedSet([1..#defining_shapes]);
  numxstab := CartesianProduct(num_shapes, stab);
  stabact := map< numxstab -> num_shapes | y:-> EltInOrb({defining_shapes[y[1],1,1]^y[2], defining_shapes[y[1],1,2]^y[2]})>;
  num_shapes := GSet(stab, num_shapes, stabact);

  H := ActionImage(stab, num_shapes);

  // We use this to act on our binary choices
  sortfn := function(x,y);
    if exists(i){i : i in [1..Degree(x)] | x[i] ne y[i]} then
      if x[i] eq 0 then
        return -1;
      else
        return 1;
      end if;
    end if;
    return 0;
  end function;
  
  binary_choices := Sort({@ v : v in VectorSpace(GF(2), #defining_shapes) @}, sortfn);
  bin_reps := Sort([ o[1] : o in Orbits(H, GSet(H, binary_choices))], sortfn);

  shapes := [];
  for b in bin_reps do
    extra := &cat[ [ [* defining_shapes[i,j,1], defining_shapes[i,j,2], IntegerToString(#defining_shapes[i,j,3]) cat (b[i] eq 0 select "A" else "B") *] : j in [1..#defining_shapes[i]] | #defining_shapes[i,j,3] eq #defining_shapes[i,1,3] ] : i in [1..Degree(b)]];
    // correct for 3B to 3C
    extra := [ x[3] eq "3B" select [* x[1], x[2], "3C" *] else x : x in extra];
    Append(~shapes, [*Ax, tau, shape cat extra *]);
  end for;

  return shapes;
end intrinsic;
/*

We define an initial object

*/
intrinsic PartialAxialAlgebra(L::List: fusion_table := MonsterFusionTable(), maximal_subgroups:=true, field:= QQ) -> ParAxlAlg
  {
  Given an L = [Ax, tau, shape] containing a GSet Ax for a group G, a map tau: Ax -> involutions of G and a shape for the algebra, we define an initial object.  shape should be given as a sequence of tuples <a, b, type>, where the axes a and b generate a subalgebra of the given type.
  }
  require Type(L[1]) eq GSetIndx and Type(L[2]) eq Map and Type(L[3]) eq SeqEnum: "The list of parameters is not in the required form.";
  return PartialAxialAlgebra(L[1],L[2],L[3]: fusion_table:=fusion_table, maximal_subgroups:=maximal_subgroups, field:=field);
end intrinsic;
/*

Build an initial partial algebra but only for basic algebras atm...

*/
intrinsic PartialAxialAlgebra(Ax::GSetIndx, tau::Map, shape::SeqEnum: fusion_table := MonsterFusionTable(), maximal_subgroups:=true, field:= QQ) -> ParAxlAlg
  {
  Given a GSet Ax for a group G, a map tau: Ax -> involutions of G and a shape for the partial algebra, we define an initial object.  shape should be given as a sequence of tuples <a, b, type>, where the axes a and b generate a subalgebra of the given type.
  
  Optional arguments:
  fusion_table is a FusTab and defaults to the Monster fusion table.
  maximal_subgroups is a Boolean and if true it tries to glue in known subalgebras with Miyamoto group a maximal subgroup of G.
  field defaults to the rationals.
  }
  require Type(fusion_table) eq FusTab: "The fuson table given is not in the required form.";
  require IsField(field): "The field given is not a field!";
    
  A := New(ParAxlAlg);
  G := Group(Ax);

  A`Wmod := GModule(G, MatrixAlgebra<field,#Ax | [PermutationMatrix(field, [Image(G.i, Ax, j) : j in [1..#Ax]]) : i in [1..#Generators(G)]]>);
  A`W := RSpace(field, Dimension(A`Wmod));
  A`number_of_axes := #Ax;

  subalgs := New(SubAlg);
  subalgs`subsps := {@ @};
  subalgs`algs := {@ @};
  subalgs`maps := [* *];

  // We calculate the full shape which is the orbit of n idempotents for nX.
  // This will help to identify which subalgebras to glue in.
  // Also set up flags for when we have glued in a subalgebra which uses the full basic algebra of that shape.
  
  full_shape := {@ < &join{@ {@ Image(rho^k, Ax, sh[1]), Image(rho^k, Ax, sh[2] ) @} : k in [0..Order(rho)-1] @}, sh[3]> where rho := (sh[1]@tau)*(sh[2]@tau): sh in shape @};
  
  A`shape := full_shape;
  shape_flags := [ false : sh in full_shape ];
  
  // We search for the maximal subgroups, check to see if we have computed these and if so glue them in.

  if maximal_subgroups then
    maxes := [ rec`subgroup : rec in MaximalSubgroups(G)];

    groups := ls("library");
    for max in maxes do
      // Check whether we have calculated that group.
      if MyGroupName(max) notin groups then
        continue max;
      end if;
      orbs := [ o : o in Orbits(max, Ax) | sub<G | o@tau> subset max];
      nums := [ eval(n) : n in ls("library/" cat MyGroupName(max))];

      // We find the subsets of axes which generate the group max, and have the same number of axes as we have previously calculated. 
      subsets := {@ o : o in Subsets({1..#orbs}) | o ne {} and &+{#orbs[i] : i in o} in nums and sub<G | (&join [orbs[i] : i in o])@tau> eq max @};
      Sort(~subsets, func<x,y| &+[ #orbs[i] : i in y] - &+[ #orbs[i] : i in x]>);
      
      // We wish to glue in the algebra which uses the largest number of axes.
      // Do we want to glue in all those we can??
      for set in subsets do
        axes := &join orbs[Setseq(set)];
        algs := ls("library/" cat MyGroupName(max) cat "/" cat IntegerToString(#axes));
        
        // We identify the shape
        type := [];  // gives the type of subalg to be glued in
        full_type := [];  // records which of the full shapes are contained in the subalg
        for i in [1..#full_shape] do
          sh := full_shape[i];
          if exists{ g : g in G | Image(g, Ax, sh[1]) subset axes} then
            Append(~type, sh[2]);
            Append(~full_type, i);
          end if;
          // A 6A, 4A, 4B could also intersect in a smaller subalgebra
          // (even if a conjugate copy intersected fully)
          if sh[2] eq "6A" then
            if exists{ g : g in G | #(Image(g, Ax, sh[1]) meet axes) eq 3} then
              Append(~type, "3A");
            elif exists{ g : g in G | #(Image(g, Ax, sh[1]) meet axes) eq 2} then
              Append(~type, "2A");
            end if;
          elif sh[2] eq "4A" and exists{ g : g in G | #(Image(g, Ax, sh[1]) meet axes) eq 2} then
            Append(~type, "2B");
          elif sh[2] eq "4B" and exists{ g : g in G | #(Image(g, Ax, sh[1]) meet axes) eq 2} then
            Append(~type, "2A");
          end if;
        end for;
        
        Sort(~type, ShapeSort);
        type := &cat type cat ".json";
        
        // We check whether we have computed it
        if type notin algs then
          continue set;
        end if;
        
        alg := LoadPartialAxialAlgebra("library/" cat MyGroupName(max) cat "/" cat IntegerToString(#axes) cat "/" cat type);
        
        // We could be trying to glue in an algebra which has collapsed
        // if so, ours also collapses
        if Dimension(alg) eq 0 then
          A := New(ParAxlAlg);
          A`Wmod := GModule(G, MatrixAlgebra<field,0|[ZeroMatrix(field,0,0) : g in Generators(G)]>);
          A`W := RSpace(field, Dimension(A`Wmod));
          A`V := A`W;
          A`fusion_table := fusion_table;
          A`shape := full_shape;
          A`number_of_axes := #Ax;
          return A;
        end if;
        
        // We first calculate the isomorphism between max and Group(alg)
        so, phi_initial := IsIsomorphic(max, Group(alg));
        assert so;
        
        // NB we might have to adjust this by an outer automorphism to get the involutions to map across correctly.

        aut := AutomorphismGroup(max);
        autFP, FPmap := FPGroup(aut);
        out, out_map := OuterFPGroup(aut);
        outPerm, perm_map := PermutationGroup(out);
        
        elts_out := [ g@@perm_map@@out_map@FPmap : g in outPerm ];
        
        // Find which axes map onto the axes in alg so we can build the gluing correctly.
        for outer in elts_out do
          phi := outer*phi_initial;
          defining_axes := [];
          for i in [1..#alg`axes] do
            if exists(j){ j : j in axes | j@tau@phi eq alg`axes[i]`inv} then
              Append(~defining_axes, j);
            else
              continue outer;
            end if;
          end for;
        end for;
        
        subsp := RSpaceWithBasis([A`W.i : i in axes]);

        glue := hom< subsp -> alg`W | Setseq(
                 &join{ { < (A.defining_axes[i]*g)`elt, (alg`axes[i]`id*(g@phi))`elt> 
                                     : g in max}
                                         : i in [1..#alg`axes] })>;

        assert forall{ <v,g> : v in Basis(subsp), g in Group(alg) |
                       ((A!v)*(g@@phi))`elt @glue eq (alg!(v@glue)*g)`elt };
        
        subalgs`subsps join:= {@ subsp @};
        if alg in subalgs`algs then
          pos := Position(subalgs`algs, alg);
        else
          subalgs`algs join:= {@ alg @};
          pos := #subalgs`algs;
        end if;
        Append(~subalgs`maps, <glue, phi^-1, pos>);
        
        // Mark that we have glued in an algebra which contains a full shape
        for i in full_type do
          shape_flags[i] := true;
        end for;
        
        // We continue onto the next maximal subgroup
        continue max;
      end for;
    end for;  
  end if;
  
  // We have now glued in all the maximal subgroups we can.
  // We check the remaining subalgebras given by the shape and if they haven't already been covered, we glue them in too.
  
  for i in [1..#full_shape] do
    if shape_flags[i] then // We have already glued in a max which covers this.
      continue i;
    end if;

    orb, type := Explode(full_shape[i]);

    subsp := RSpaceWithBasis([ A`W.i : i in orb]);
    subalgs`subsps join:= {@ subsp @};

    alg := LoadPartialAxialAlgebra("library/basic_algebras/" cat type);
    if alg in subalgs`algs then
      pos := Position(subalgs`algs, alg);
    else
      subalgs`algs join:= {@ alg @};
      pos := #subalgs`algs;
    end if;

    // We need to find an isomorphism from the group of the basic algebra to the subgroup of A
    // By assumption, the basic algebras have their first and second elements as generating idempotents.
    
    a0 := orb[1]@tau;
    a1 := orb[2]@tau;
    
    _, alg_tau := Axes(alg);
    alg_a0 := alg.1@alg_tau;
    alg_a1 := alg.2@alg_tau;

    // We find the involutions associated to the generating elements of the basic algebra, so we can identify the same rho

    homg := hom< Group(alg) -> Group(A) | [<alg_a0, a0>, <alg_a1, a1>]>;
    assert forall(t){ <g,h> : g,h in Generators(Group(alg)) | (g*h)@homg eq (g@homg)*(h@homg)};

    alg_rho := alg_a0*alg_a1;
    // assert alg_rho eq (a0*a1) @@ homg;
    
    // We can now build the ordered basis.
    alg_bas := &join {@ {@ alg | alg.1*alg_rho^k, alg.2*alg_rho^k @} : k in [0..Order(alg_rho)-1] @};

    map := hom< subsp -> alg`W | Matrix(field, [ Eltseq(v) : v in alg_bas]) >;

    Append(~subalgs`maps, < map, homg, pos >);
  end for;

  A`subalgs := subalgs;
  A`V := sub<A`W|>;
  
  A`fusion_table := fusion_table;
  inv_classes := Sort({@ Representative(o) : o in Orbits(G, Ax) @});
  A`axes := [AssignAxis(A, Ax, tau, i) : i in inv_classes];

  A`mult := [];
  A`rels := {@ @};
  
  return ForceGrading(A);
end intrinsic;
/*

Assigns an axis

*/
intrinsic AssignAxis(A::ParAxlAlg, Ax::GSet, tau::Map, a::RngIntElt) -> Axis
  {
  Assigns the axes to A.
  }
  G := Group(A`Wmod);
  require G eq Group(Ax): "The group associated to W and the axes are not the same.";
  W := A`W;

  idem := New(AxlAxis);
  idem`id := A.a;
  H := Stabiliser(G, Ax, a);
  idem`stab := H;
  assert a@tau in Centre(H);
  idem`inv := a@tau;

  Ggr, gr := Grading(A`fusion_table); 
  require Order(Ggr) in {1,2}: "The fusion table is not Z_2-graded.";

  idem`odd := AssociativeArray();
  idem`even := AssociativeArray();
  eigenvalues := A`fusion_table`eigenvalues;

  if Order(Ggr) eq 2 then
    preim := { lambda : lambda in eigenvalues | lambda @ gr eq Ggr.1 };
    for S in { IndexedSet(S) : S in Subsets(preim) | S ne {} } do
      idem`odd[S] := sub<W|>;
    end for;
  end if;

  preim := { lambda : lambda in eigenvalues | lambda @ gr eq Ggr!1 };
  for S in Subsets(preim) do
    idem`even[Sort(IndexedSet(S), EigenvalueSort)] := sub<W|>;
  end for;

  return idem;
end intrinsic;

intrinsic NewGInvariantSubspace(WH::ModGrp, W::ModTupFld, S::.) -> ModTupFld
  {
  Returns the subspace of W spanned by S which is invariant under the action of the group associated to the G-module WH.
  }
  t := Cputime();
  require Type(S) in {SetIndx, SetEnum, SeqEnum}: "The given elements are not in a set or sequence.";
  if Type(Universe(S)) eq ParAxlAlg then
    SS := {@ s`elt : s in S @};
  elif Type(Universe(S)) eq ModTupFld then
    SS := S;
  elif Type(Universe(S)) eq ModGrp then
    SS := S;
  else
    error "S is not a set of vectors or partial axial algebra elements.";
  end if;
  require forall{ s : s in SS | IsCoercible(WH,s)}: "The set of elements given are not coercible into the given G-module.";
  
  Hmat := [ Matrix(h) : h in MatrixGroup(WH)];
  
  oldU := sub<W|>;
  newU := sub<W|S>;
  while oldU ne newU do
    oldU := newU;
    newU +:= sub<W| &join [ FastMatrix({@ v : v in Basis(newU)@}, h) : h in Hmat]>;
  end while;
  
  if Cputime(t) ge 1 then
    vprintf ParAxlAlg, 4: "Time taken for GInvariantSubspace is %o.  Starting number of objects %o, ending dim %o.\n", Cputime(t), #S, Dimension(newU);
  end if;
  return newU;
end intrinsic;

intrinsic GInvariantSubspace(WH::ModGrp, W::ModTupFld, S::.) -> ModTupFld
  {
  Returns the subspace of W spanned by S which is invariant under the action of the group associated to the G-module WH.
  }
  t := Cputime();
  require Type(S) in {SetIndx, SetEnum, SeqEnum}: "The given elements are not in a set or sequence.";
  if #S eq 0 then
    return sub<W|>;
  end if;
  if Type(Universe(S)) eq ParAxlAlg then
    SS := {@ s`elt : s in S @};
  elif Type(Universe(S)) eq ModTupFld then
    SS := S;
  elif Type(Universe(S)) eq ModGrp then
    SS := S;
  else
    error "S is not a set of vectors or partial axial algebra elements.";
  end if;
  require forall{ s : s in SS | IsCoercible(WH,s)}: "The set of elements given are not coercible into the given G-module.";
  U := sub<WH | SS>;
  UU := sub< W | [W | W!(WH!u) : u in Basis(U)]>;
  if Cputime(t) ge 1 then
    vprintf ParAxlAlg, 4: "Time taken for GInvariantSubspace is %o.  Starting number of objects %o, ending dim %o.\n", Cputime(t), #S, Dimension(UU);
  end if;
  return UU;
end intrinsic;
/*

Internal function for updating the axes.

*/
intrinsic UpdateAxes(A::ParAxlAlg, ~Anew::ParAxlAlg, psi::Map: matrix := Matrix(BaseField(A), Dimension(A), Dimension(Anew), [u@psi : u in Basis(A`W)]))
  {
  If psi is a map from the subspace for A to the subspace for Anew, then build the axes for Anew from those of A.  NB we require psi to be a G-invariant map (although it is given as a map on the subspaces).  Takes an optional argument of the matrix of psi.
  }
  dims := CheckEigenspaceDimensions(A);

  // We collect up all the basis vectors for all the eigenspaces and find their images all at once
  allkeys := AssociativeArray();
  allkeys["even"] := [{@ @}, {@ 1 @}, {@ 0 @}, {@ 1/4 @}, {@ 1, 0 @}, {@ 1, 1/4 @}, {@ 0, 1/4 @}, {@ 1, 0, 1/4 @}];
  allkeys["odd"] := [{@ 1/32 @}];
  L := &cat[ Basis(A`axes[i]``attr[k]) : k in allkeys[attr], attr in ["even", "odd"], i in [1..#A`axes]];
  
  images := FastFunction(L, psi: matrix:=matrix);

  Wnew := Anew`W;
  axes := [];
  offset := 0;
  tt := Cputime();
  for i in [1..#A`axes] do
    newaxis := New(AxlAxis);
    newaxis`stab := A`axes[i]`stab;
    newaxis`inv := A`axes[i]`inv;
    newaxis`id := Anew!((A`axes[i]`id)`elt @ psi);
    
    for attr in ["even", "odd"] do
      newaxis``attr := AssociativeArray();
      for k in allkeys[attr] do
        // Since psi is G-invariant, we do not need to do GInvariantSubspace
        newaxis``attr[k] := sub<Wnew | images[offset+1..offset+Dimension(A`axes[i]``attr[k])]>;
        offset +:= Dimension(A`axes[i]``attr[k]);
      end for;
    end for;   
    Append(~axes, newaxis);
  end for;
  printf "Time: %o\n", Cputime(tt);
  Anew`axes := axes;
end intrinsic;
/*

Internal function to update the subalgebras.

*/
intrinsic UpdateSubalgebras(A::ParAxlAlg, ~Anew::ParAxlAlg, psi::Map : algs := A`subalgs`algs, maps := A`subalgs`maps)
  {
  If psi is a map from the subspace for A to the subspace for Anew, then build the subalgebras for Anew from those of A.  We require psi to be G-invariant.  If given, algs is a list of new subalgebras and maps is a list of the corresponding new maps.
  }
  W := A`W;
  Wnew := Anew`W;
  newsubsps := {@ Parent(Wnew) | @};
  newmaps := [* *];
  
  for i in [1..#A`subalgs`subsps] do
    subsp := A`subalgs`subsps[i];
    map, homg, pos := Explode(maps[i]);
    alg := algs[pos];

    // We calculate the restriction of psi to subsp so we ensure that the preimage of newsubsp lies in subsp
  
    psi_rest := hom<subsp->Wnew | [ v@psi : v in Basis(subsp)]>;
    
    require Dimension((Kernel(psi_rest)@map)) eq 0: "You need to quotient out the new subalgebra first.";

    newsubsp := sub<Wnew | [Wnew | u@psi_rest : u in Basis(subsp)]>;
    newmap := hom< newsubsp -> alg`W | [ u@@psi_rest@map : u in Basis(newsubsp)]>;
    Include(~newsubsps, newsubsp);
    Append(~newmaps, <newmap, homg, pos>);
  end for;
  
  subalgs := New(SubAlg);
  subalgs`subsps := newsubsps;
  subalgs`maps := newmaps;
  subalgs`algs := algs;
  Anew`subalgs := subalgs;
end intrinsic;
