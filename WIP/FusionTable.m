/*

Defines a fusion table and the necessary function to use it.

*/
declare type FusTab;

declare attributes FusTab:
  eigenvalues,  // a SetIndx of eigenvalues
  table,        // table of values for the fusion table
  useful,       // a SetIndx of tuples of the useful fusion rules
  group,        // a GrpPerm which is the grading on the table
  grading;      // a map from the values to the group giving the grading

intrinsic 'eq'(A::FusTab, B::FusTab) -> BoolElt
  {
  Checks whether the eigenvalues and table are the same.
  }
  return A`eigenvalues eq B`eigenvalues and A`table eq B`table;
end intrinsic;
/*

Pretty printing for Fusion tables!

*/
intrinsic Print(T::FusTab)
  {
  Prints a fusion table.
  }
  L := T`table;
  obj := T`eigenvalues;
  
  top := [ " " cat Sprint(x) cat " " : x in obj ];
  width1st := Max([#t : t in top]);
  table := [ [Sprintf("%*o|", width1st, top[i])] cat [Substring(Sprint(L[i,j]), 3, #Sprint(L[i,j])-4) : j in [1..#L[i]]] : i in [1..#L]];
  widths := [ Max([#table[i,j] : i in [1..#table]] cat [j eq 1 select 0 else #top[j-1]]) : j in [1..#table+1]];
  top_table := [[ " "^(widths[1]-1) cat "|"] cat top] cat [[ "-"^widths[i] : i in [1..#widths] ]] cat table;
  for j in [1..#top_table] do
    for i in [1..#widths] do
      printf "%*o", widths[i], top_table[j,i];
    end for;
    printf "\n";
  end for;
end intrinsic;
/*

Calculates the grading for the table.

*/
intrinsic Grading(T::FusTab) -> GrpPerm, Map
  {
  Calculates the grading group G and the grading function gr:F -> G.
  }
  if assigned T`group then
    return T`group, T`grading;
  end if;
  // We form a group whose generators are the eigenvalues and relations given by the table to find the grading.
  // Any eigenvalues which are in a set which is an entry in the fusion table must have the same grading
  evals := T`eigenvalues;
  entries := {@ S : S in Flat(T`table) | S ne {@@} @};
  Sort(~entries,func<x,y|#y-#x>);
  gens := [* e : e in entries *];
  for e in entries do
    gens := [* #(e meet g) ne 0 select e join g else g : g in gens *];
  end for;
  gens := {@ g : g in gens @};
  
  // We set up a function to give the generator number of an eigenvalue
  genno := AssociativeArray();
  for e in evals do
    assert exists(i){g : g in gens | e in g };
    genno[e] := Position(gens, i);
  end for;
  
  F := FreeAbelianGroup(#gens);
  rels := [ F.genno[1] ];
  
  // We build some relations
  e1 := gens[genno[1]];
  for i in e1 do
    for j in evals diff e1 do
      for prod in T`table[Position(evals,i), Position(evals,j)] do
        Append(~rels, F.genno[j] - F.genno[prod]);
      end for;
    end for;
  end for;
  for i in evals diff e1 do
    for j in evals diff e1 do
      for prod in T`table[Position(evals,i), Position(evals,j)] do
        Append(~rels, F.genno[i] + F.genno[j] - F.genno[prod]);
        Append(~rels, F.genno[j] + F.genno[i] - F.genno[prod]);
      end for;
    end for;
  end for;
  
  G, map := quo<F|rels>;
  assert Order(G) le #evals;
  GG, iso := PermutationGroup(G);
  T`group := GG;
  T`grading := map< evals -> GG | i:-> (F.genno[i] @map)@@iso>;
  return T`group, T`grading;
end intrinsic;
/*

Calculates the useful fusion rules.

*/
intrinsic UsefulFusionRules(T::FusTab) -> SetIndx
  {
  Returns those fusion rules for a Z_2-graded table which are useful.
  }
  if assigned T`useful then
    return T`useful;
  end if;
  evals := T`eigenvalues;
  G, grad := Grading(T);
  require Order(G) eq 2: "The group is %o-graded.", G;
  pos := {@ i : i in evals | i @ grad eq G!1 @};
  subsets := {@ S : S in Subsets(Set(pos)) | S ne {} @};
  Sort(~subsets, func< x,y | #y-#x>);

  FT := [ [] : i in [1..#subsets]];
  for i in [1..#subsets] do
    for j in [1..i] do
      FT[i,j] := &join { T`table[Position(evals,k), Position(evals,l)] : k in subsets[i], l in subsets[j] };
      FT[j,i] := FT[i,j];
    end for;
  end for;
  
  T`useful := {@ @};
  for i in [1..#subsets] do
    row := Set(FT[i]);
    for S in row do
      pos := Position(FT[i], S);
      assert exists(j){ j : j in [1..i] | FT[j,pos] eq FT[i,pos]};
      if j ne 1 or pos ne 1 then
        if i le pos then
          Include(~T`useful, < subsets[pos], subsets[j], Set(FT[j,pos])>);
        else
          Include(~T`useful, < subsets[j], subsets[pos], Set(FT[j,pos])>);
        end if;
      end if;
    end for;
  end for;
  
  return T`useful;
end intrinsic;
/*

Returns the Monster fusion table.

*/
intrinsic MonsterFusionTable() -> FusTab
  {
  Returns the fusion table for the Monster.
  }
  T := New(FusTab);
  T`eigenvalues := {@ 1, 0, 1/4, 1/32 @};
  T`table := [[ {@1@}, {@ @}, {@1/4@}, {@1/32@}], [ {@@}, {@ 0 @}, {@1/4@}, {@1/32@}], [ {@1/4@}, {@1/4 @}, {@1,0@}, {@1/32@}], [ {@1/32@}, {@1/32@}, {@1/32@}, {@1,0,1/4@}]];
  _ := UsefulFusionRules(T);
  
  return T;
end intrinsic;
/*

Returns the extended Jordan-type table.

*/
intrinsic HyperJordanTypeFusionTable(eta::FldRatElt) -> FusTab
  {
  Returns the fusion table of extended Jordan-type eta.
  }
  T := New(FusTab);
  T`eigenvalues := {@ 1, 0, 2*eta, eta @};
  T`table := [[ {@1@}, {@ @}, {@2*eta@}, {@eta@}], [ {@@}, {@ 0 @}, {@2*eta@}, {@eta@}], [ {@2*eta@}, {@2*eta @}, {@1,0@}, {@eta@}], [ {@eta@}, {@eta@}, {@eta@}, {@1,0,2*eta@}]];
  _ := UsefulFusionRules(T);
  
  return T;
end intrinsic;