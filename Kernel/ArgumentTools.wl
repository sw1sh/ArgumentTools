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


f_[Coidentity] ^:= f;


SetAttributes[Cocomposition, {Flat, OneIdentity}];


f_[Cocomposition[x_, y_]] ^:= f[y][x];


Cocomposition[Coidentity, y_] := Cocomposition[y];


Cocomposition[x_, Coidentity] := Cocomposition[x];


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
