/*

Functions for loading and saving a ParAxlAlg as a json object

*/
import "ParAxlAlg.m": library_location;
/*

Code to implement a group name which will work in older versions of magma too.  

*/
intrinsic MyGroupName(G::GrpPerm) -> MonStgElt
  {
  If GroupName is defined in magma (roughly version 2.21 or above) it returns GroupName, otherwise it returns order_num, where <order, num> is given by IdentifyGroup.
  }
  try
    name := eval("GroupName(G)");
  catch e
    ord, num := Explode(IdentifyGroup(G));
    name := Sprintf("%o_%o", ord, num);
  end try;
  return name;
end intrinsic;
/*

Given a filename, return a sequence of the dihedral subalgebra types

*/
intrinsic ParseShape(name::MonStgElt) -> SetMulti
  {
  Given a filename, return a sequence of the dihedral subalgebra types.
  }
  type := {**};
  while #name ne 0 and name[1] in {"2","3","4","5","6"} do
    Include(~type, name[1..2]);
    name := name[3..#name];
  end while;
  return type;
end intrinsic;
/*

A function for choosing the filename

*/
intrinsic Filename(A::ParAxlAlg) -> MonStgElt
  {
  Returns a filename of the form
  
  library_location/field/MyGroupName/number_of_axes/shape_i.json
  
  or
  
  library_location/field/MyGroupName/number_of_axes/shape_i_partial.json
  
  if the algebra has not been fully reduced, where i is an index allowing different tau maps.
  }
  shapetype := &cat [ sh[2] : sh in A`shape];
  num_axes := &cat [ Sprintf("%o+", #o) : o in Orbits(Group(A`GSet), A`GSet)];
  num_axes := num_axes[1..#num_axes-1];
  
  // We must check to see if the file already exists, so we know how to get the i right for different taus.  We assume that there is no other matching algebra ie that i:=1
  i := 1;
  
  // first check to see if the directory exists at all
  
  path := Sprintf("%o/%m/%o/%o", library_location, BaseField(A), MyGroupName(Group(A)), num_axes);
  if ExistsPath(path) then
    // we must now see if there is already an algebra with the same path with a different tau.
    algs := ls(path);
    shapes := [ ParseShape(sh) : sh in algs];
    possibles := {@ i : i in [1..#shapes] | shapes[i] eq ParseShape(shapetype) @};
    
    if #possibles ne 0 then
      so := false;
      for j in possibles do
        alg_type := GetTypePartialAxialAlgebra(Sprintf("%o/%o", path, algs[j]));
        _, alg_ax, alg_tau, alg_shape := Explode(alg_type);
        
        so := IsIsomorphic(alg_ax, alg_tau, alg_shape, A`GSet, A`tau, A`shape);
        if so then
          shapetype := algs[j][1..#shapetype];
          i := algs[j][#shapetype+2];
          break j;
        end if;
      end for;
      if not so then
        // We must choose an i which doesn't conflict with those already there
        conflicts := {@ a : a in algs | a[1..#shapetype] eq shapetype @};
        eyes := { a[#shapetype+2] : a in conflicts };
        i := Min({1..#eyes+1} diff eyes);
      end if;
    end if;
  end if;
  
  if Dimension(A) eq Dimension(A`V) then
    return path cat Sprintf("/%o_%o.json", shapetype, i);
  else
    return path cat Sprintf("/%o_%o_partial.json", shapetype, i);
  end if;  
end intrinsic;
/*

Provide some directory functions for magma

*/
ls_script := "
import os
import sys

filename = sys.argv[1]

print \"/\".join(os.listdir(filename))
";

intrinsic ls(dirname::MonStgElt) -> SeqEnum
  {
  ls
  }
  string := Pipe(Sprintf("python -c '%o' '%o'", ls_script, dirname), "");
  return Split(string, "\n/");
end intrinsic;

exists_script := "
import os
import sys

filename = sys.argv[1]

print os.path.isdir(filename)
";

intrinsic ExistsPath(dirname::MonStgElt) -> BoolElt
  {
  Returns whether the directory given by dirname exists.
  }
  string := Pipe(Sprintf("python -c '%o' '%o'", exists_script, dirname), "");
  if string eq "True\n" then
    return true;
  else
    return false;
  end if;
end intrinsic;
//
// =============== Code to save a ParAxlAlg ================
//
/*

Saves a partial axial algebra

*/
intrinsic SavePartialAxialAlgebra(A::ParAxlAlg: filename:=Filename(A))
  {
  Saves a partial axial algebra in JSON format.  Saves by default using the Filename function.
  }
  vprintf ParAxlAlg, 2: "Saving partial axial algebra...";
  
  // We check to see if the path exists and if not create it.
  paths := Split(filename, "/");
  path := &cat[ p cat "/" : p in paths[1..#paths-1]];
  System(Sprintf("mkdir -p '%o'", path));
  
  PrintFile(filename, JSON(A): Overwrite:=true);
  vprintf ParAxlAlg, 2: " complete!\n";
end intrinsic;
/*

Code to serialise some types that will be useful

*/
intrinsic JSON(x::ParAxlAlgElt : nl:="\n") -> MonStgElt
  {
  Serialise a partial axial algebra element as a sequence.
  }
  return JSON(x`elt: nl:=nl);
end intrinsic;

intrinsic JSON(x::ModTupFldElt : nl:="\n") -> MonStgElt
  {
  Serialise a vector as a sequence.
  }
  return JSON(Eltseq(x): nl:=nl);
end intrinsic;

intrinsic JSON(x::ModTupFld : nl:="\n") -> MonStgElt
  {
  Serialise a vector (sub)space as a sequence of basis elements.
  }
  return JSON(Basis(x): nl:=nl);
end intrinsic;

intrinsic JSON(x::Set : nl:="\n") -> MonStgElt
  {
  Serialise a set as a sequence.
  }
  return JSON(Setseq(x));
end intrinsic;
/*

Main code to serialise a ParAxlAlg

*/
intrinsic JSON(A::ParAxlAlg: subalgs:=0) -> MonStgElt
  {
  Serialise a partial axial algebra as a JSON object.
  
  There is an optional flag, subalgs.  If 1 then it saves all subalgebra information recursively, if 0 it only saves the subalgebras of the top algebra and if -1 it doesn't save any.  The default is 0.
  }
  return JSON(ParAxlAlgToList(A: subalgs := subalgs));
end intrinsic;


intrinsic ParAxlAlgToList(A::ParAxlAlg: subalgs:=0) -> List
  {
  Converts a partial axial algebra to a list prior to serialising as a JSON object.
  
  There is an optional flag, subalgs.  If 1 then it saves all subalgebra information recursively, if 0 it only saves the subalgebras of the top algebra and if -1 it doesn't save any.  The default is 0.
  }
  G := Group(A);
  gen := GeneratorsSequence(G);
  act := Action(G, A`GSet);
  orb_reps := {@ o[1] : o in Orbits(G, A`GSet) @};
  
  alg := [* *];
  Append(~alg, <"class", "Partial axial algebra">);

  Append(~alg, <"field", Sprintf("%m", BaseField(A))>);
  Append(~alg, <"GSet", [* [*gen[i], gen[i]@act*] : i in [1..#gen] *]>);
  Append(~alg, <"tau", [* [* i, i@A`tau *] : i in orb_reps *]>);
  Append(~alg, <"shape", [* [* sh[1], sh[2] *] : sh in A`shape *]>);
  
  gen_mat := ActionGenerators(A`Wmod);
  assert #gen eq #gen_mat;
  Append(~alg, <"Wmod", [* [* gen[i], gen_mat[i] *] : i in [1..#gen] *]>);
  
  Append(~alg, <"V", A`V>);
  
  Append(~alg, <"table", FusTabToList(A`fusion_table)>);
  
  if not assigned A`mult then
    assert Dimension(A) eq 0;
    return alg;
  end if;
  
  Append(~alg, <"GSet_to_axes", [* [* Position(Image(A`GSet_to_axes), A`axes[i]`id`elt), i *] : i in [1..#A`axes] *]>);
  
  Append(~alg, <"mult", A`mult>);
  
  axes := [];
  for i in [1..#A`axes] do
    axes[i] := AssociativeArray();
    axes[i]["id"] := A`axes[i]`id;
    axes[i]["stab"] := GeneratorsSequence(A`axes[i]`stab);
    axes[i]["inv"] := A`axes[i]`inv;
    axes[i]["even"] := A`axes[i]`even;
    axes[i]["odd"] := A`axes[i]`odd;
  end for;
  Append(~alg, <"axes", axes>);

  if assigned A`subalgs and subalgs ge 0 then
    Append(~alg, <"subalgs", SubAlgToList(A`subalgs :subalgs:= subalgs eq 1 select 1 else subalgs-1)>);
  end if;
  
  if assigned A`rels then
    Append(~alg, <"rels", Setseq(A`rels)>);
  end if;
  return alg;
end intrinsic;
/*

Code to serialise a subalgebra

*/
intrinsic SubAlgToList(x::SubAlg: subalgs := -1) -> List
  {
  Transform a Subalgebra to a List prior to serialising as a JSON.
  }
  alg := [* *];

  Append(~alg, <"subsps", x`subsps>);
  
  maps := [];
  for i in [1..#x`maps] do
    map, homg, pos := Explode(x`maps[i]);
    maps[i] := [* [* [* x, x@map *] : x in Basis(Domain(map))*],
                        [* [*x, x@homg *] : x in Generators(Domain(homg))*],
                        pos*];
  end for;
  Append(~alg, <"maps", maps>);

  Append(~alg, <"algs", [ParAxlAlgToList(alg: subalgs:=subalgs) : alg in x`algs]>);

  return alg;
end intrinsic;
/*

Code to serialise a fusion table

*/
intrinsic FusTabToList(x::FusTab) -> List
  {
  Transform a fusion table to a List prior to serialising as a JSON.
  }
  alg := [* *];
  Append(~alg, <"class", "Fusion table">);
  
  Append(~alg, <"eigenvalues", Setseq(x`eigenvalues)>);
  Append(~alg, <"table", x`table>);
  
  return alg;
end intrinsic;
//
// =============== Code to load a ParAxlAlg ================
//
/*

Loads just enough of the file to get the shape info

*/
intrinsic GetTypePartialAxialAlgebra(filename::MonStgElt) -> Tup
  {
  Partially load the axial algebra given by filename and return a tuple of the field, GSet, tau-map and shape.
  }
  vprint ParAxlAlg, 2: "Partially Loading partial axial algebra...";
  paths := Split(filename, "/");
  if "." notin paths[#paths] then
    realfilename := filename cat ".json";
  else
    realfilename := filename;
  end if;

  file := Open(filename, "r");
  text := "";
  line := "";
  // We wish to read everything up to GSet_to_axes
  while "Wmod" notin line do
    line := Gets(file);
    text cat:= line;
  end while;
  delete file;
  
  pos := Position(text, "Wmod");
  assert exists(i){ i : i in Reverse([1..#text]) | i le pos and text[i] eq ","};
  text := text[1..i-1] cat "}";
  
  alg := ParseJSON(text);
  keys := Keys(alg);
  require "class" in keys and alg["class"] eq "Partial axial algebra": "The file given does not encode a partial axial algebra.";
  require keys eq {"class", "field", "GSet", "tau", "shape"}: "The file doesn't contain the shape information in the top part";
  
  F := eval(alg["field"]);
  gens := [Numbers(k[1]) : k in alg["GSet"]];
  images := [Numbers(k[2]) : k in alg["GSet"]];
  n := Max(gens[1]);
  G := PermutationGroup<n | gens>;
  m := Max(images[1]);
  act := hom<G -> Sym(m) | [<G!gens[i], Sym(m)!images[i]> : i in [1..#gens]]>;
  
  Ax := IndexedSet([1..m]);
  AxxG := CartesianProduct(Ax, G);
  f := map<AxxG -> Ax | y:-> y[1]^(y[2]@act)>;
  Ax := GSet(G, Ax, f);
  
  images := [];
  for k in alg["tau"] do
    o := Orbit(G, Ax, k[1]);
    gs := [ g where _,g := IsConjugate(G, Ax, k[1], i) : i in o];
    images cat:= [<o[i],(G!Numbers(k[2]))^gs[i]> : i in [1..#o]];
  end for;
  
  tau := map<Ax->G | images>;
  
  shape := [ < {@ i : i in Numbers(sh[1])@}, sh[2]> : sh in alg["shape"] ];
  
  return <F, Ax, tau, shape>;  
end intrinsic;
/*

Load

*/
intrinsic LoadPartialAxialAlgebra(filename::MonStgElt) -> ParAxlAlg
  {
  Loads a partial axial algebra from the location given.
  }
  vprintf ParAxlAlg, 2: "Loading partial axial algebra...";
  paths := Split(filename, "/");
  if "." notin paths[#paths] then
    realfilename := filename cat ".json";
  else
    realfilename := filename;
  end if;
  
  string := Read(realfilename);
  alg := ParseJSON(string);
  vprintf ParAxlAlg, 2: " complete!\n";
  return PartialAxialAlgebra(alg);
end intrinsic;

intrinsic PartialAxialAlgebra(alg::Assoc) -> ParAxlAlg
  {
  Creates a partial axial algebra A from an associative array.  We assume that the associative array represents A stored in json format.
  }
  keys := Keys(alg);
  require "class" in keys and alg["class"] eq "Partial axial algebra": "The file given does not encode a partial axial algebra.";
  
  A := New(ParAxlAlg);
  
  F := eval(alg["field"]);
  gens := [Numbers(k[1]) : k in alg["GSet"]];
  images := [Numbers(k[2]) : k in alg["GSet"]];
  n := Max(gens[1]);
  G := PermutationGroup<n | gens>;
  m := Max(images[1]);
  act := hom<G -> Sym(m) | [<G!gens[i], Sym(m)!images[i]> : i in [1..#gens]]>;
  
  Ax := IndexedSet([1..m]);
  AxxG := CartesianProduct(Ax, G);
  f := map<AxxG -> Ax | y:-> y[1]^(y[2]@act)>;
  Ax := GSet(G, Ax, f);
  A`GSet := Ax;
  
  images := [];
  for k in alg["tau"] do
    o := Orbit(G, Ax, k[1]);
    gs := [ g where _,g := IsConjugate(G, Ax, k[1], i) : i in o];
    images cat:= [<o[i], (G!Numbers(k[2]))^gs[i]> : i in [1..#o]];
  end for;
  
  A`tau := map<Ax->G | images>;
  
  A`shape := [ < {@ i : i in Numbers(sh[1])@}, sh[2]> : sh in alg["shape"] ];

  A`number_of_axes := n;

  dim := #alg["Wmod"][1,2];
  A`Wmod := GModule(G, MatrixAlgebra<F, dim | [ Matrix(F,alg["Wmod"][i,2]) : i in [1..#gens]]>);

  A`W := RSpace(F, Dimension(A`Wmod));
  A`V := sub<A`W | [Numbers(v): v in alg["V"]]>;

  require "class" in Keys(alg["table"]) and alg["table"]["class"] eq "Fusion table": "The file given does not have a valid fusion table.";
  FT := New(FusTab);
  FT`eigenvalues := IndexedSet(Numbers(alg["table"]["eigenvalues"]));
  FT`table := [ [ IndexedSet(Numbers(S)) : S in row ] : row in alg["table"]["table"]];
  A`fusion_table := FT;

  if "mult" notin keys then
    assert Dimension(A) eq 0;
    A`GSet_to_axes := map<Ax -> A`W | i :-> A`W!0>;
    return A;
  end if;
  
  A`mult := [ [ A`W!Numbers(row): row in mat ]: mat in alg["mult"]];

  if "subalgs" in keys then
    subalgs := New(SubAlg);
    subalgs`subsps := [* sub<A`W | [Numbers(v) : v in bas]> : bas in alg["subalgs"]["subsps"] *];
    subalgs`algs := {@ PartialAxialAlgebra(x) : x in alg["subalgs"]["algs"] @};
    
    subalgs`maps := [* *];
    for i in [1..#alg["subalgs"]["maps"]] do
      map_list, homg_list, pos := Explode(alg["subalgs"]["maps"][i]);
      map := hom<subalgs`subsps[i] -> subalgs`algs[pos]`W | [ <Numbers(t[1]), Numbers(t[2])> : t in map_list]>;
      
      H := sub<G | [G!Numbers(t[1]) : t in homg_list]>;
      homg := hom< H -> Group(subalgs`algs[pos]) | [ <Numbers(t[1]), Numbers(t[2])> : t in homg_list]>;
      Append(~subalgs`maps, <map, homg, pos>);
    end for;
    A`subalgs := subalgs;
  end if;
  
  A`axes := [];
  for i in [1..#alg["axes"]] do
    idem := New(AxlAxis);
    idem`id := A!Numbers(alg["axes"][i]["id"]);
    idem`stab := sub<G | [G| G!Numbers(x) : x in alg["axes"][i]["stab"]]>;
    idem`inv := G!Numbers(alg["axes"][i]["inv"]);
    
    idem`even := AssociativeArray();
    for k in Keys(alg["axes"][i]["even"]) do
      idem`even[eval(k)] := sub<A`W | [A`W | A`W!Numbers(x) : x in alg["axes"][i]["even"][k]]>;
    end for;

    idem `odd := AssociativeArray();    
    for k in Keys(alg["axes"][i]["odd"]) do
      idem`odd[eval(k)] := sub<A`W | [A`W | A`W!Numbers(x) : x in alg["axes"][i]["odd"][k]]>;
    end for;
    Append(~A`axes, idem);
  end for;
  
  // We provide a function from the GSet to W
  images := [];
  for pair in alg["GSet_to_axes"] do
    i, j := Explode(pair);
    o := Orbit(G, Ax, i);
    gs := [ g where _, g := IsConjugate(G, Ax, i, k) : k in o];
    images cat:= [ < o[k], (A`axes[j]`id*gs[k])`elt> : k in [1..#o]];
  end for;
  A`GSet_to_axes := map<Ax -> A`W | images>;  
  
  if "rels" in keys then
    A`rels := {@ A`W | A`W!Numbers(v) : v in alg["rels"] @};
  end if;
  
  return A;
end intrinsic;
/*

Loads all axial algebras with a given group

*/
intrinsic LoadAllGroup(G::GrpPerm :field := Rationals(), library := library_location, partial:=false) -> SeqEnum
  {
  Returns all partial axial algebras with group G.
  }
  return LoadAllGroup(GroupName(G): field := field, library:=library, partial:=partial);
end intrinsic;

intrinsic LoadAllGroup(grp_name::MonStgElt :field := Rationals(), library := library_location, partial:=false) -> SeqEnum
  {
  Returns all partial axial algebras with groupname grp_name.
  }
  path := Sprintf("%o/%m/%o", library, field, grp_name);
  if not ExistsPath(path) then
    return [];
  end if;
  L := [];
  for num in Sort(ls(path)) do
    shapes := Sort(ls(Sprintf("%o/%o", path, num)));
    for filename in shapes do
      if partial or "_partial" notin filename then
        Append(~L, LoadPartialAxialAlgebra(Sprintf("%o/%o/%o", path, num, filename)));
      end if;
    end for;
  end for;
  
  return L;
end intrinsic;
