(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Wolfram`ArgumentTools`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


Coidentity
Cozero
Cocomposition
Coconstruct
Coapply
RightCocomposition
Cosequence
Held
Argument


Begin["`Private`"];


(* ::Section:: *)
(*Coidentity*)


(f_Symbol)[Coidentity] /; Developer`SymbolQ[f] && FreeQ[Attributes[f], HoldFirst | HoldAll] ^:= f

(f : HoldPattern[Function[_]])[Coidentity] ^:= f

(f : HoldPattern[Function[_, _]])[Coidentity] ^:= f

(f : HoldPattern[Function[_, _, attrs_]])[Coidentity] /; FreeQ[attrs, HoldFirst | HoldAll] ^:= f

(f : Except[_Function])[Coidentity] /; ! Developer`SymbolQ[f] ^:= f


(* ::Section:: *)
(*Cozero*)


(f_Symbol)[Cozero] /; Developer`SymbolQ[f] && FreeQ[Attributes[f], HoldFirst | HoldAll] ^:= Cozero

(f : HoldPattern[Function[_]])[Cozero] ^:= Cozero

(f : HoldPattern[Function[_, _]])[Cozero] ^:= Cozero

(f : HoldPattern[Function[_, _, attrs_]])[Cozero] /; FreeQ[attrs, HoldFirst | HoldAll] ^:= Cozero

(f : Except[_Function])[Cozero] /; ! Developer`SymbolQ[f] ^:= Cozero


(* ::Section:: *)
(*Cocomposition*)


SetAttributes[Cocomposition, {Flat, OneIdentity, SequenceHold}]

(f_Symbol)[Cocomposition[x_, y_]] /; Developer`SymbolQ[f] && FreeQ[Attributes[f], HoldFirst | HoldAll] ^:= f[y][x]

(f : HoldPattern[Function[_]])[Cocomposition[x_, y_]] ^:= f[y][x]

(f : HoldPattern[Function[_, _]])[Cocomposition[x_, y_]] ^:= f[y][x]

(f : HoldPattern[Function[_, _, attrs_]])[Cocomposition[x_, y_]] /; FreeQ[attrs, HoldFirst | HoldAll] ^:= f[y][x]

(f : Except[_Function])[Cocomposition[x_, y_]] /; ! Developer`SymbolQ[f] ^:= f[y][x]

Cocomposition[Coidentity, y_] := Cocomposition[y]

Cocomposition[x_, Coidentity] := Cocomposition[x]

(* Use Verbatim to prevent infinite recursion due to the Flat attribute *)
Verbatim[Cocomposition][x_] := x

Verbatim[Cocomposition][] := Coidentity


(* ::Section:: *)
(*RightCocomposition*)


SetAttributes[RightCocomposition, {Flat, OneIdentity, SequenceHold}]

(f_Symbol)[RightCocomposition[x_, y_]] /; Developer`SymbolQ[f] && FreeQ[Attributes[f], HoldFirst | HoldAll] ^:= f[x][y]

(f : HoldPattern[Function[_]])[RightCocomposition[x_, y_]] ^:= f[x][y]

(f : HoldPattern[Function[_, _]])[RightCocomposition[x_, y_]] ^:= f[x][y]

(f : HoldPattern[Function[_, _, attrs_]])[RightCocomposition[x_, y_]] /; FreeQ[attrs, HoldFirst | HoldAll] ^:= f[x][y]

(f : Except[_Function])[RightCocomposition[x_, y_]] /; ! Developer`SymbolQ[f] ^:= f[x][y]

RightCocomposition[Coidentity, y_] := RightCocomposition[y]

RightCocomposition[x_, Coidentity] := RightCocomposition[x]

(* Use Verbatim to prevent infinite recursion due to the Flat attribute *)
Verbatim[RightCocomposition][x_] := x

Verbatim[RightCocomposition][] := Coidentity


(* ::Section:: *)
(*Cosequence*)


(* Coidentity at the end should have no effect, but don't want it
   to disappear prematurely in the recursive definition below. *)
Cosequence[fs___][xs__, Coidentity] := Cosequence[fs][xs]

Cosequence[f_, fs___][x_, xs___] := Sequence[f[x], Cosequence[fs][xs]]

Cosequence[fs__][] := fs

Cosequence[][xs___] := xs


(* ::Section:: *)
(*Coconstruct*)


Coconstruct[x_, f_] := f[x]

Coconstruct[x_, f_, fs__] := Sequence[f[x], Coconstruct[x, fs]]

Coconstruct[x_][fs__] := Coconstruct[x, fs]

Coconstruct[x_][] := x


(* ::Section:: *)
(*Coapply*)


Options[Coapply] = Options[Apply]

Coapply[x_, f_, lvl :  _Integer | {_Integer} | {_Integer, _Integer} | Infinity : {0}, opts : OptionsPattern[]] := Apply[f, x, lvl, opts]

Coapply[x_][f_] := Apply[f, x]


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


(* ::Section:: *)
(*Argument*)


Options[Argument] = Options[Comap]

f_[Argument[x_, lvl : _Integer | {_Integer} | {_Integer, _Integer} | Infinity : {-1}, opts : OptionsPattern[]]] ^:= Comap[f, x, lvl, opts]


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
