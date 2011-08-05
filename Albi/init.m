(* ::Package:: *)

BeginPackage["Calculus`Albi`"];


Begin["`Private`"];
If[Head[Calculus`CWD]===String,
	SINDirectory=Calculus`CWD<>"Albi\\",
	SINDirectory=NotebookDirectory[]
];
Get[SINDirectory<>"Rational\\init.m"];
Get[SINDirectory<>"Risch\\init.m"];
(*Get[SINDirectory<>"SIN-like\\init.m"];*)
End[];


EndPackage[];


(*Int[E^x,x]
Int[x^4*(1-x^2)^(-5/2),x]
Int[x^(1/2)*(1+x)^(5/2),x]
Int[Log[3*(4*(5+6*x)^7)^2],x]
Int[(x^3)^(-1/3),x]
Int[x E^x]*)

(*Int[(a+b*Sqrt[x])^20/Sqrt[x],x]*)
(*Int[(1-2 Sqrt[x])^20/Sqrt[x],x]*)
