(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Wolfram`ArgumentTools`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


Coidentity;
Cocomposition;


Begin["`Private`"];


(* ::Section:: *)
(*Definitions*)


(f : Except[_Function])[Coidentity] /; ! Developer`SymbolQ[Unevaluated[f]] || ! MemberQ[Attributes[f], HoldFirst | HoldAll] ^:= f

(f : Verbatim[Function][_, _, attrs___])[Coidentity] /; ! MemberQ[Flatten[{attrs}], HoldFirst | HoldAll] ^:= f



SetAttributes[Cocomposition, {Flat, OneIdentity}]

(f : Except[_Function])[Cocomposition[args___]] /; ! Developer`SymbolQ[Unevaluated[f]] || ! MemberQ[Attributes[f], HoldFirst | HoldAll] ^:=
    Fold[Construct, Prepend[f] @ Reverse[Hold[args]]]


Cocomposition[left___, Coidentity, right___] := Cocomposition[left, right]



(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
