(* ::Package:: *)

BeginPackage["Calculus`Albi`Rational`"];
HermiteReduce::usage="";
LogToAtan::usage="";
Log2ArcTan::usage="";


Begin["`Private`"];
If[Head[Calculus`CWD]===String,
	RatDirectory=Calculus`CWD<>"Albi\\Rational\\",
	RatDirectory=NotebookDirectory[]
];
Get[RatDirectory<>"Rioboo.m"];
Get[RatDirectory<>"intSubRat.m"]
End[];


EndPackage[];
