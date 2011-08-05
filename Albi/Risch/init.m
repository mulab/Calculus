(* ::Package:: *)

BeginPackage["Calculus`Albi`Risch`"];
pmint;


Begin["`Private`"];
If[Head[Calculus`CWD]===String,
	RischDIR=Calculus`CWD<>"Albi\\Risch\\",
	RischDIR=NotebookDirectory[]
];
Get[RischDIR<>"AlgebraicPrelim.m"];
Get[RischDIR<>"Misc.m"];
Get[RischDIR<>"RationalIntegration.m"];
Get[RischDIR<>"RischDE.m"];
Get[RischDIR<>"ParametricProblems.m"];
Get[RischDIR<>"CoupledDESystem.m"];
Get[RischDIR<>"SymbolicIntBook.m"];
Get[RischDIR<>"pmint.m"];
End[];


EndPackage[];
