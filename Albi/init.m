(* ::Package:: *)

BeginPackage["Calculus`Albi`"]


Begin["`Private`"]
If[Head[Calculus`CWD]===String,
	SINDirectory=Calculus`CWD<>"Albi\\",
	SINDirectory=NotebookDirectory[]
];
Get[SINDirectory<>"Rioboo.m"];
Get[SINDirectory<>"Risch\\init.m"];
End[];


EndPackage[];


(*pmint[E^x,x]
pmint[x^4*(1-x^2)^(-5/2),x]
pmint[x^(1/2)*(1+x)^(5/2),x]
pmint[Log[3*(4*(5+6*x)^7)^2],x]
pmint[(x^3)^(-1/3),x]
pmint[x E^x]*)

(*pmint[(a+b*Sqrt[x])^20/Sqrt[x],x]*)
(*pmint[(1-2 Sqrt[x])^20/Sqrt[x],x]*)
