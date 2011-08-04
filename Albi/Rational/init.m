(* ::Package:: *)

BeginPackage["Calculus`Albi`Rational`"];
HermiteReduce::usage="";
LogToAtan::usage="";


Begin["`Private`"];
If[Head[Calculus`CWD]===String,
	RatDirectory=Calculus`CWD<>"Albi\\Rational\\",
	RatDirectory=NotebookDirectory[]
];
Get[RatDirectory<>"Rioboo.m"];
End[];


EndPackage[];
