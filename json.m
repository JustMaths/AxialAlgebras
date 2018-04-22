/*

Code for saving and loading magma objects to/from JSON format.
Written by Michael Fryers, 2016.
Edited by Justin McInroy 2017.

*/

ZZ := Integers();

QQ := Rationals();

map := func<f,l| [f(x):x in l] >;
indent := " ";

maxline := 200;

// Utilities

function makeseq(open, elts, sep, close, nl)
  if &and["\n" notin s : s in elts] then
  short := open cat " " cat Join(elts, sep cat " ") cat " " cat close;
    if #short le maxline then return short; end if;
  end if;
  newnl := nl cat indent;
  return open cat newnl cat Join(elts, sep cat newnl) cat nl cat close;
end function;

intrinsic AssociativeArray(x::List) -> Assoc
  {
  Convert a list of pairs into an associative array.
  }
  A := AssociativeArray();
  for p in x do
    require #p eq 2 : "Ill—formed pair in AssociativeArray";
    A[p[1]] := p[2];
  end for;
  return A;
end intrinsic;

// Generic structures

intrinsic JSON(x::Assoc : nl:="\n") -> MonStgElt
  {
  Serialise an associative array as a JSON object.
  }
  newnl := nl cat indent;

  keys := [ k : k in Keys(x)];
  try
    Sort(~keys);
  catch e;
  end try;

  strs := [ Sprintf("\"%o\": %o", k, JSON(x[k] : nl:=newnl)) : k in keys ];

  return makeseq("{", strs, ",", "}", nl);
end intrinsic;

intrinsic JSON(x::List : nl:="\n") -> MonStgElt
  {
  Serialise a list: if the first element is a pair then we take it to be <key, value> pairs and
produce a JSON object; otherwise we produce a JSON array.
  Note that an empty list is serialised as "[ ]", never as "\{ \}".
  }
  newnl := nl cat indent;
  if #x gt 0 and Type(x[1]) eq Tup and #x[1] eq 2 then
    require forall{true:t in x|Type(t) eq Tup and #t eq 2}: "Ill—formed pair—list in JSON";
    strs := [ Sprintf("\"%o\": %o", t[1], JSON(t[2] : nl:=newnl)) : t in x ];
    return makeseq("{", strs, ",", "}", nl);
  else
    return makeseq("[", [JSON(y : nl:=newnl):y in x], ",", "]", nl);
  end if;
end intrinsic;

intrinsic JSON(x::SeqEnum : nl:="\n") -> MonStgElt
  {
  Serialise a sequence in the same way as for a list.
  }
  return JSON([* e:e in x *] : nl:=nl);
end intrinsic;

// Atoms

intrinsic JSON(x::MonStgElt : nl:="\n") -> MonStgElt
  {
  Serialise a string. We cope with ASCII printables, newlines, and tabs.
  }
  y := "";
  for c in Eltseq(x) do
    if c eq "\"" or c eq "\\" then y cat:= "\\" cat c;
    elif c eq "\n" then y cat:= "\\n";
    elif c eq "\t" then y cat:= "\\t";
    else y cat:= c;
    end if;
  end for;
  return "\"" cat y cat "\"";
end intrinsic;

intrinsic JSON(x::RngIntElt : nl:="\n") -> MonStgElt
  {
  Serialise an integer.
  }
  return IntegerToString(x);
end intrinsic;

intrinsic JSON(x::FldRatElt : nl:="\n") -> MonStgElt
  {
  Serialise a rational. If it's an integer, serialise as an integer, otherwise as a string.
  }
  return x in ZZ select IntegerToString(ZZ!x) else Sprintf("\"%o\"", x);
end intrinsic;

intrinsic JSON(x::RngIntResElt : nl:="\n") -> MonStgElt
  {
  Serialise an integer-mod, as an integer.
  }
  return IntegerToString(ZZ!x);
end intrinsic;

intrinsic JSON(x::FldFinElt : nl:="\n") -> MonStgElt
  {
  Serialise an element of a finite field of prime order, as an integer.
  }
  return IntegerToString(ZZ!x);
end intrinsic;

intrinsic JSON(x::BoolElt : nl:="\n") -> MonStgElt
  {
  Serialise a Boolean.
  }
  return Sprintf("%o", x);
end intrinsic;

intrinsic JSON(x::Tup : nl:="\n") -> MonStgElt
  {
  Serialise an empty tuple, representing JSON null.
  }
  require #x eq 0 : "Only empty tuples (representing null) accepted in JSON";
  return "null";
end intrinsic;

// Permutations

intrinsic JSON(x::GrpPermElt : nl:="\n") -> MonStgElt
  {
  Serialise a permutation as a sequence.
  }
  return JSON(Eltseq(x) : nl:=nl);
end intrinsic;

// Matrices

intrinsic JSON(x::AlgMatElt : nl:="\n") -> MonStgElt
  {
  Serialise a matrix (over ZZ, QQ, or GF(p)) as an array of arrays.
  }
  if NumberOfRows(x) eq 0 and NumberOfColumns(x) eq 0 then
    return "[ ]";
  end if;
  B := BaseRing(x);
  require IsField(B) select IsPrimeField(B) else B eq ZZ : "Base ring of matrix must be ZZ, QQ, or GF(p) in JSON";
  rs := [Eltseq(r):r in Rows(x)];
  strs := [[x in ZZ select IntegerToString(ZZ!x) else Sprintf("\"%o\"",x):x in r]:r in rs];
  f := Sprintf("%%%oo", Max([#s:s in r,r in strs]));
  strs := [[Sprintf(f,s):s in r]:r in strs];
  newnl := nl cat indent;
  return "[" cat newnl cat Join(["[ " cat Join(r, ", ") cat " ]":r in strs], "," cat newnl) cat nl cat "]";
end intrinsic;

// Useful functions for undoing JSONisation

intrinsic Keys(x::List) -> SeqEnum
  {
  Returns the sequence of indices of x.
  }
  return [1..#x];
end intrinsic;

intrinsic Numbers(x::Any) -> Any
  {
  Try to turn x into a rational or nested sequence of rationals.
  }
  if Type(x) eq List then
    return [Numbers(y):y in x];
  elif Type(x) eq MonStgElt and Regexp("^0|-?[1-9][0-9]*(/[1-9][0-9]*)?$", x) then
    x := StringToRational(x);
    return x in ZZ select ZZ!x else x;
  else
    return x;
  end if;
end intrinsic;

intrinsic Num(x::Any) -> FldRatElt
  {
  Convert a string into a rational, or return x if it is not a string.
  }
  if Type(x) eq MonStgElt then
    return StringToRational(x);
  else
    return x;
  end if;
end intrinsic;

intrinsic Matrix(R::Rng, M::List) -> Any
  {
  Convert a JSONised matrix into a matrix over R.
  }
  return Matrix(R, [[R!Num(x):x in r]:r in M]);
end intrinsic;

/*
Deserialisation

Uses external call to python to convert JSON to Magma—readable form.

Modifying this script?
Escape all double quote and backslash characters.
Don't use single quotes anywhere in the script!
*/
pyscript := "
import json
import re
from sys import stdin, version_info

if version_info[0] >= 3:
  long = int
  unicode = str

def escape(s):
  return \"\\\"\" + re.sub(r\"([\\\\\\\"])\", r\"\\\\\\1\", s) + \"\\\"\"

def magma(o):
  t = type(o)
  if t is int or t is long:
    return str(o)
  if t is str or t is unicode:
    return escape(o)
  if t is float:
    return str(o)
  if t is bool:
    return \"true\" if o else \"false\"
  if o is None:
    return \"null\"
  if t is list:
    return \"[*\" + \",\".join(magma(x) for x in o) + \"*]\"
  if t is dict:
    return \"dict([*\" + \",\".join(escape(k) + \",\" + magma(v) for k,v in o.items()) + \"*])\"
  raise TypeError(\"cannot Magmatise %s object\"%t)

o = json.load(stdin)

print(magma(o))
";

intrinsic ParseJSON(s::MonStgElt) -> Any
  {
  Deserialise a JSON string to an object.
  This uses a Python script to convert JSON to Magma-readable form.
  }
  function dict(l)
    d := AssociativeArray();
    for i in [1..#l by 2] do
      k := l[i]; v := l[i+1];
      assert k notin Keys(d);
      d[k] := v;
    end for;
    return d;
  end function;
  null := <>;
  inf := Infinity();
  nan := <"nan">;
  return eval(Pipe("python -c '" cat pyscript cat "'",s));
end intrinsic;
