/*

Functions for loading and saving a ParAxlAlg as a json object

*/
import "ParAxlAlg.m": library_location;
// ---------------------
// Code to save a ParAxlAlg
/*

Code to implement a group name which will work in older versions of magma too.  

*/
intrinsic MyGroupName(G::GrpPerm) -> MonStgElt
  {
  If GroupName is definied in magma (roughly version 2.21 or above) it returns GroupName, otherwise it returns order_num, where <order, num> is given by IdentifyGroup.
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

A function for choosing the filename

*/
intrinsic Filename(A::ParAxlAlg) -> MonStgElt
  {
  Returns a filename of the form
  
  library_location/MyGroupName/number_of_axes/shape.json
  
  or
  
  library_location/MyGroupName/number_of_axes/shape_partial.json
  
  if the algebra has not been fully reduced.
  }
  shape := &cat [ sh[2] : sh in A`shape];
  
  path := Sprintf("%o/%o/%o/%o", library_location, MyGroupName(Group(A)), A`number_of_axes, shape);
  if Dimension(A) eq Dimension(A`V) then
    return path cat ".json";
  else
    return path cat "_partial.json";
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
  
  There is an optional flag, subalgs.  If 1 then it saves all subalgebra information recursively, if 0 it only saves the subalgebras of the top algebra and if -1 it doesn't save any.  The default is -1.
  }
  return JSON(ParAxlAlgToList(A: subalgs := subalgs));
end intrinsic;


intrinsic ParAxlAlgToList(A::ParAxlAlg: subalgs:=0) -> List
  {
  Converts a partial axial algebra to a list prior to serialising as a JSON object.
  
  There is an optional flag, subalgs.  If 1 then it saves all subalgebra information recursively, if 0 it only saves the subalgebras of the top algebra and if -1 it doesn't save any.  The default is -1.
  }
  alg := [* *];
  Append(~alg, <"class", "Partial axial algebra">);
  
  Append(~alg, <"shape", [* [* sh[1], sh[2] *] : sh in A`shape *]>);
  Append(~alg, <"number_of_axes", A`number_of_axes>);
  
  //require BaseField(A) eq Rationals(): "Currently can only save alegbras over the rationals.";
  Append(~alg, <"field", Sprintf("%m", BaseField(A))>);
  gen := GeneratorsSequence(Group(A));
  gen_mat := ActionGenerators(A`Wmod);
  assert #gen eq #gen_mat;
  Append(~alg, <"Wmod", [* [* gen[i], gen_mat[i] *] : i in [1..#gen] *]>);
  
  Append(~alg, <"V", A`V>);
  
  Append(~alg, <"table", FusTabToList(A`fusion_table)>);
  
  if not assigned A`mult then
    assert Dimension(A) eq 0;
    return alg;
  end if;
    
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

  Append(~alg, <"subsps", Setseq(x`subsps)>);
  
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
//-----------------------------------------
// Code to load a ParAxlAlg

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
  gens := [ Numbers(k[1]) : k in alg["Wmod"]];
  n := Max(gens[1]);
  G := PermutationGroup<n | gens>;
  dim := #alg["Wmod"][1,2];
  A`Wmod := GModule(G, MatrixAlgebra<F, dim | [ Matrix(F,alg["Wmod"][i,2]) : i in [1..#gens]]>);

  A`W := RSpace(F, Dimension(A`Wmod));
  A`V := sub<A`W | [Numbers(v): v in alg["V"]]>;
  
  A`shape := {@ < {@ i : i in sh[1]@}, sh[2]> : sh in alg["shape"] @};
  A`number_of_axes := alg["number_of_axes"];

  require "class" in Keys(alg["table"]) and alg["table"]["class"] eq "Fusion table": "The file given does not have a valid fusion table.";
  FT := New(FusTab);
  FT`eigenvalues := IndexedSet(Numbers(alg["table"]["eigenvalues"]));
  FT`table := [ [ IndexedSet(Numbers(S)) : S in row ] : row in alg["table"]["table"]];
  A`fusion_table := FT;

  if "mult" notin keys then
    assert Dimension(A) eq 0;
    return A;
  end if;
  
  A`mult := [ [ A`W!Numbers(row): row in mat ]: mat in alg["mult"]];

  if "subalgs" in keys then
    keys_subalg := Keys(alg["subalgs"]);
    subalgs := New(SubAlg);
    subalgs`subsps := {@ sub<A`W | [Numbers(v) : v in bas]> : bas in alg["subalgs"]["subsps"] @};
    subalgs`algs := {@ PartialAxialAlgebra(x) : x in alg["subalgs"]["algs"] @};
    subalgs`maps := [* < 
        hom<subalgs`subsps[i] -> subalgs`algs[triple[3]]`W | [ <Numbers(t[1]), Numbers(t[2])> : t in triple[1]]>,
        hom<Group(subalgs`algs[triple[3]]) -> G | [ <Numbers(t[1]), Numbers(t[2])> : t in triple[2]]>,
        triple[3] > where triple := alg["subalgs"]["maps"][i] : i in [1..#alg["subalgs"]["maps"]] *];
    A`subalgs := subalgs;
  end if;
  
  A`axes := [];
  for i in [1..#alg["axes"]] do
    idem := New(AxlAxis);
    idem`id := A!Numbers(alg["axes"][i]["id"]);
    idem`stab := sub<G | [G| G!Numbers(x) : x in alg["axes"][i]["stab"]]>;
    idem`inv := G!Numbers(alg["axes"][i]["inv"]);
    idem`WH := Restriction(A`Wmod, idem`stab);
    
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
  
  if "rels" in keys then
    A`rels := {@ A`W | A`W!Numbers(v) : v in alg["rels"] @};
  end if;
  
  return A;
end intrinsic;
/*

Loads all axial algebras with a given group

*/
intrinsic LoadAllGroup(G::GrpPerm :library := library_location, partial:=true) -> SeqEnum
  {
  Returns all partial axial algebras with group G.
  }
  if not MyGroupName(G) in ls(library) then
    return [];
  end if;
  L := [];
  for num in Sort(ls(Sprintf("%o/%o", library, MyGroupName(G)))) do
    shapes := Sort(ls(Sprintf("%o/%o/%o", library, MyGroupName(G), num)));
    for filename in shapes do
      if partial or "_partial" notin filename then
        Append(~L, LoadPartialAxialAlgebra(Sprintf("%o/%o/%o/%o", library, MyGroupName(G), num, filename)));
      end if;
    end for;
  end for;
  
  return L;
end intrinsic;
