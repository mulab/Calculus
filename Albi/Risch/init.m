(* ::Package:: *)

BeginPackage["Calculus`Risch`"];
pmint::usage="pmint[f,x] returns integral of f";


Begin["`Private`"];
SetDirectory[NotebookDirectory[]];
Get["AlgebraicPrelim.m"];
Get["Misc.m"];
Get["RationalIntegration.m"];
Get["RischDE.m"];
Get["ParametricProblems.m"];
Get["CoupledDESystem.m"];
Get["SymbolicIntBook.m"];
Get["pmint.m"];
End[];


EndPackage[];
