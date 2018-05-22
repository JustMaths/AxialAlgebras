/*

Functions for creating an initial object

*/
QQ := Rationals();
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
//
// ================ BUILD A PARTIAL AXIAL ALGEBRA =================
//
/*

We define an initial object

*/
intrinsic PartialAxialAlgebra(L::List: fusion_table := MonsterFusionTable(), maximal_subgroups:=true, partial := false, field:= QQ) -> ParAxlAlg
  {
  Given an L = [Ax, tau, shape] containing a GSet Ax for a group G, a map tau: Ax -> involutions of G and a shape for the algebra, we define an initial object.  shape should be given as a sequence of tuples <o, type>, where the axes o[1] and o[2] generate a subalgebra of the given type with axes o.
  }
  require Type(L[1]) eq GSetIndx and Type(L[2]) eq Map and Type(L[3]) eq SeqEnum: "The list of parameters is not in the required form.";
  return PartialAxialAlgebra(L[1],L[2],L[3]: fusion_table:=fusion_table, maximal_subgroups:=maximal_subgroups, field:=field);
end intrinsic;
/*

Build an initial partial algebra but only for basic algebras atm...

*/
intrinsic PartialAxialAlgebra(Ax::GSetIndx, tau::Map, shape::SeqEnum: fusion_table := MonsterFusionTable(), maximal_subgroups:=true, partial := false, field:= QQ) -> ParAxlAlg
  {
  Given a GSet Ax for a group G, a map tau: Ax -> involutions of G and a shape for the partial algebra, we define an initial object.  shape should be given as a sequence of tuples <o, type>, where the axes o[1] and o[2] generate a subalgebra of the given type with axes o.
  
  Optional arguments:
  fusion_table is a FusTab and defaults to the Monster fusion table.
  maximal_subgroups is a Boolean and if true it tries to glue in known subalgebras with Miyamoto group a maximal subgroup of G.
  field defaults to the rationals.
  }
  require Type(fusion_table) eq FusTab: "The fuson table given is not in the required form.";
  require IsField(field): "The field given is not a field!";
    
  A := New(ParAxlAlg);
  A`GSet := Ax;
  A`tau := tau;
  A`shape := shape;
  A`number_of_axes := #Ax;
  A`fusion_table := fusion_table;
  G := Group(Ax);

  A`Wmod := PermutationModule(G, Action(G, Ax), field); 
  A`W := RSpace(field, Dimension(A`Wmod));
  Wmod := A`Wmod;
  W := A`W;
  A`GSet_to_axes := map<Ax -> W | i :-> W.i>;

  subalgs := New(SubAlg);
  subalgs`subsps := [* *];
  subalgs`algs := {@ @};
  subalgs`maps := [* *];

  // We calculate the full shape which is the orbit of n idempotents for nX.
  // This will help to identify which subalgebras to glue in.
  // Also set up flags for when we have glued in a subalgebra which uses the full basic algebra of that shape.

  shape_flags := [ false : sh in shape ];
  
  // We search for the maximal subgroups, check to see if we have computed these and if so glue them in.

  if maximal_subgroups then
    // find which subalgebras we can glue in
    maxsubalgs, flags := MaximalGluingSubalgebras(Ax, tau, shape: field := field, gluing:=true);
    
    for maxsubalg in maxsubalgs do
      file, glue, homg := Explode(maxsubalg);
      alg := LoadPartialAxialAlgebra(file);

      // We could be trying to glue in an algebra which has collapsed
      // If so, ours also collapses
      if Dimension(alg) eq 0 then
        A`Wmod := GModule(G, MatrixAlgebra<field,0|[ZeroMatrix(field,0,0) : g in Generators(G)]>);
        A`W := RSpace(field, Dimension(A`Wmod));
        A`V := A`W;
        A`GSet_to_axes := map<Ax -> A`W | i :-> W!0>;
        return A;
      end if;
        
      axes := Domain(glue);
      tau_images := [ i@tau : i in axes];
      H := sub<G | tau_images>;
      
      subsp := RSpaceWithBasis([A`W.i : i in axes]);

      map := hom< subsp -> alg`W | [i@glue@alg`GSet_to_axes : i in axes]>;
      
      homg := hom< H -> Group(alg) | [< g, g@homg> : g in FewGenerators(H)]>;

      assert forall{ <v,g> : v in Basis(subsp), g in H |
                       ((A!v)*(g))`elt @map eq (alg!(v@map)*(g@homg))`elt };
        
      subalgs`subsps cat:= [* subsp *];
      if alg in subalgs`algs then
        pos := Position(subalgs`algs, alg);
      else
        subalgs`algs join:= {@ alg @};
        pos := #subalgs`algs;
      end if;
      Append(~subalgs`maps, <map, homg, pos>);
        
      // Mark that we have glued in an algebra which contains a full shape
      Or(~shape_flags, flags);
    end for;
  end if;
  
  // We have now glued in all the maximal subgroups we can.
  // We check the remaining subalgebras given by the shape and if they haven't already been covered, we glue them in too.
  
  for i in [1..#shape] do
    if shape_flags[i] then // We have already glued in a max which covers this.
      continue i;
    end if;

    orb, type := Explode(shape[i]);

    subsp := RSpaceWithBasis([ A`W.i : i in orb]);
    subalgs`subsps cat:= [* subsp *];

    alg := LoadPartialAxialAlgebra(Sprintf("library/%m/basic_algebras/%o", field, type));
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
    
    alg_tau := alg`tau;    
    alg_a0 := 1@alg_tau;
    alg_a1 := 2@alg_tau;

    // We find the involutions associated to the generating elements of the basic algebra, so we can identify the same rho
    
    D := sub<G | a0, a1>;
    homg := hom< D -> Group(alg) | [<a0, alg_a0>, <a1, alg_a1>]>;
    assert forall(t){ <g,h> : g,h in Generators(D) | (g*h)@homg eq (g@homg)*(h@homg)};

    alg_rho := alg_a0*alg_a1;
    if a0 ne G!1 and a1 ne G!1 then
      assert alg_rho eq (a0*a1) @ homg;
    else
      // There is at least one identity element
      assert type in {"2A", "2B"};
    end if;
    
    // We can now build the ordered basis.
    alg_bas := &join {@ {@ alg | alg.1*alg_rho^k, alg.2*alg_rho^k @} : k in [0..Order(alg_rho)-1] @};

    map := hom< subsp -> alg`W | Matrix(field, [ Eltseq(v) : v in alg_bas]) >;

    Append(~subalgs`maps, < map, homg, pos >);
  end for;

  A`subalgs := subalgs;
  A`V := sub<A`W|>;
  
  inv_classes := Sort({@ Representative(o) : o in Orbits(G, Ax) @});
  A`axes := [AssignAxis(A, Ax, tau, i) : i in inv_classes];

  A`mult := [];
  A`rels := {@ @};
  PullbackEigenvaluesAndRelations(New(ParAxlAlg), ~A: force_all:=true);
  
  // We force the grading and do the wh-w trick as we assume this has been done before an expansion
  A := ForceGrading(A);
  
  max_size := Max([#S : S in Keys(A`axes[1]`even)]);
  assert exists(evens){S : S in Keys(A`axes[1]`even) | #S eq max_size};
  
  for i in [1..#A`axes] do
    actionhom := GModuleAction(A`Wmod);
    Hmat := [ h@actionhom - IdentityMatrix(field, #Ax) : h in A`axes[i]`stab | h ne G!1];
    
    prods := [ FastMatrix({@ w : w in Basis(A`axes[i]`even[evens])@}, h) : h in Hmat];
    A`axes[i]`even[evens diff {@1@}] +:= sub< W | &join prods >;
  end for;
  
  return A;
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
  idem`even[{1}] := sub<W | idem`id`elt>;

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
//
// ================ UPDATE A PARTIAL AXIAL ALGEBRA ================
//
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
  newsubsps := [* *];
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
    Append(~newsubsps, newsubsp);
    Append(~newmaps, <newmap, homg, pos>);
  end for;
  
  subalgs := New(SubAlg);
  subalgs`subsps := newsubsps;
  subalgs`maps := newmaps;
  subalgs`algs := algs;
  Anew`subalgs := subalgs;
end intrinsic;
/*

Pull back the relations and eigenvectors from the subalgebras.

*/
intrinsic PullbackEigenvaluesAndRelations(A::ParAxlAlg, ~Anew::ParAxlAlg: force_all:=false)
  {
  Given a new partial axial algebra, Anew, pull back the relations and eigenvectors from its subalgebras.  If the option force_all is true, then we do this for all eigenvectors.  If false, then we just do it for those eigenvectors seen in the gluing maps of Anew, but not A.
  }
  Ggr := Anew`fusion_table`group;
  grading := Anew`fusion_table`grading;
  evals := Anew`fusion_table`eigenvalues;
  require Order(Ggr) le 2: "The algebra is more than Z_2-graded.";
  
  allkeys := AssociativeArray();
  allkeys["even"] := Subsets({ e : e in evals | e@grading eq Ggr!1});
  allkeys["odd"] := Subsets({ e : e in evals | e@grading eq Ggr.1}) diff {{}};
  
  G := Group(Anew);
  Wnew := Anew`W;
  
  for i in [1..#Anew`subalgs`subsps] do
    newmap, homg, pos := Explode(Anew`subalgs`maps[i]);
    alg := Anew`subalgs`algs[pos];
    
    vprint ParAxlAlg, 4: "Collecting relations";
    // We could either use GInvariantSubspace here or InduceGAction.
    // Sometimes InduceGAction is much longer than just forming a G-submodule.
    // But often it is a bit quicker, but not that much.  Don't really understand this.
    /*
    time U := GInvariantSubspace(Anew`Wmod, Wnew, Basis(Kernel(newmap)));
    time bas := {@ Wnew | u : u in &cat InduceGAction(G, Group(alg)@homg, actionhom, Basis(Kernel(newmap))) @};
    assert sub<Wnew | bas> eq U;
    */
    U := GInvariantSubspace(Anew`Wmod, Wnew, Basis(Kernel(newmap)));
    Anew`rels join:= {@ Wnew | u : u in Basis(U)@};
    
    Im_sp := Image(newmap);
    
    // if we are forcing all eigenvalues to be pulled back, then 
    if force_all then
      Im_old := sub<alg`W|>;
    else
      Im_old := Image(A`subalgs`maps[i,1]);
    end if;
    
    if Dimension(Im_sp) eq Dimension(Im_old) then
      continue;
    end if;
    vprint ParAxlAlg, 4: "Pulling back eigenvectors from the subalgebra.";
    
    // NB Im_sp is a H-submodule of alg, where H = Group(alg).  If an axis id of A is conjugate to an axis of alg by g, then the double coset KgH, where K = Stab(id) are all the elements which conjugate id to an axis of alg (of a given type). There could be additional outer automorphisms of alg induced by G, but we would see these in A and they would just fuse classes of axes in alg.  So, we need only find a single g to conjugate the eigenspaces.

    if not assigned axes then
      axes := [ Position(Image(Anew`GSet_to_axes), Anew`axes[j]`id`elt) : j in [1..#Anew`axes]];
    end if;
    
    alg_axes := [ Position(Image(Anew`GSet_to_axes), alg`axes[j]`id`elt@@newmap) : j in [1..#alg`axes]];
    
    // S is a set of tuples <j,k,g>, where the jth axis of Anew conjugates via g to the k^th axis of alg
    S := {@ <j,k,g> : j in [1..#Anew`axes], k in [1..#alg`axes] | so
              where so, g := IsConjugate(G, Anew`GSet, axes[j], alg_axes[k]) @};
         
    // Precompute the pullback matrix from Im_sp to Wnew
    pullback_mat := Matrix([(Basis(Im_sp)[l])@@newmap : l in [1..Dimension(Im_sp)]]);
    
    for s in S do
      j,k,g := Explode(s);
      // gather together all the eigenvectors needed and precompute the maps required
      // We only need to do those which are in Im_sp, but not Im_old
      
      eigvects := [];
      dims := AssociativeArray();
      for attr in ["even", "odd"], key in allkeys[attr] do
        eig_old := alg`axes[k]``attr[key] meet Im_old;
        bas := ExtendBasis(eig_old, alg`axes[k]``attr[key] meet Im_sp);
        dims[key] := #bas - Dimension(eig_old);
        eigvects cat:= [ Coordinates(Im_sp, v) : v in bas[Dimension(eig_old)+1..#bas]];
      end for;
      
      // We could have no new eigenvectors
      if #eigvects eq 0 then
        continue s;
      end if;
      
      // We pull back the vectors to A, apply g^-1
      if not assigned actionhom then
        actionhom := GModuleAction(Anew`Wmod);
      end if;
      
      newvects := [Matrix(eigvects)*pullback_mat*((g^-1)@actionhom)];
      
      // Im_sp is a Group(alg)-submodule, so for each eigenspace U, U meet Im_sp is an alg`axes[k]`stab submodule.  So the pullback to A is an alg`axes[k]`stab@homg module.
      
      H := (alg`axes[k]`stab@@homg)^(g^-1);
      Htrans := Transversal(Anew`axes[j]`stab, H);
      
      for h in Htrans diff {@ Id(G)@} do
        Append(~newvects, newvects[1]*(h@actionhom));
      end for;
      
      offset := 0;
      for attr in ["even", "odd"], key in allkeys[attr] do
        Anew`axes[j]``attr[key] +:= sub<Wnew | &cat [ newvects[l][offset+1.. offset+dims[key]] : l in [1..#newvects]]>;
        offset +:= dims[key];
      end for;
    end for;
  end for;
end intrinsic;
