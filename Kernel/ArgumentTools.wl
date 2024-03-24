(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Wolfram`ArgumentTools`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


Coidentity
Cocomposition
Held


Begin["`Private`"];


(* ::Section:: *)
(*Coidentity*)


(f_Symbol)[Coidentity] /; Developer`SymbolQ[f] && FreeQ[Attributes[f], HoldFirst | HoldAll] ^:= f

(f : HoldPattern[Function[_, _]])[Coidentity] ^:= f

(f : HoldPattern[Function[_, _, attrs_]])[Coidentity] /; FreeQ[attrs, HoldFirst | HoldAll] ^:= f

(f : Except[_Function])[Coidentity] /; ! Developer`SymbolQ[f] ^:= f


(* ::Section:: *)
(*Cocomposition*)


SetAttributes[Cocomposition, {Flat, OneIdentity}]

(f_Symbol)[Cocomposition[x_, y_]] /; Developer`SymbolQ[f] && FreeQ[Attributes[f], HoldFirst | HoldAll] ^:= f[y][x]

(f : Except[_Function])[Cocomposition[x_, y_]] /; ! Developer`SymbolQ[f] ^:= f[y][x]

Cocomposition[Coidentity, y_] := Cocomposition[y]

Cocomposition[x_, Coidentity] := Cocomposition[x]


(* ::Section:: *)
(*Held*)


HoldRangeFromAttributes[attrs_, len_] :=
    Which[
        MemberQ[attrs, HoldAll | HoldAllComplete] || ContainsAll[attrs, {HoldFirst, HoldRest}],
        {1, len},
        MemberQ[attrs, HoldFirst],
        {1, 1},
        MemberQ[attrs, HoldRest],
        {2, len},
        True,
        {1, 0}
    ]

HoldRange[sym_Symbol[args___]] := HoldRangeFromAttributes[Attributes[sym], Length[HoldComplete[args]]]
HoldRange[Verbatim[Function][_, _, attrs___][args___]] := HoldRangeFromAttributes[Flatten[{attrs}], Length[HoldComplete[args]]]
HoldRange[_[___]] := {1, 0}
HoldRange[___] := Missing["Position"]


SetAttributes[Held, HoldAllComplete]

Held /: expr : head_[left___, Held[mid_], right___] := With[{
    holdRange = HoldRange[Unevaluated[expr]],
    unHeldAll = Replace[Unevaluated @ Unevaluated[head[left, mid, right]], Verbatim[Held][h_] :> h, {2}]
},
	MapAt[
		Unevaluated,
		unHeldAll,
		If[holdRange[[1]] > 1, ;; holdRange[[1]] - 1, holdRange[[2]] + 1 ;;]
	]
]


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
