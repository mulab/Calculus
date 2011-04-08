(* ::Package:: *)

(*Initialize*)
SetDirectory[NotebookDirectory[]];
Import["intSubPow.m"];
Import["intSubFra.m"];
Import["intSubRfs.m"];



(*TestTable*)
AL={
(*{Function,{parameters},output form}*)
{Plus,{1,1,2,3},7},
(*\:5bf9\:79ef\:5206\:8f6c\:6362\:ff0c\:8f6c\:5316\:540e\:5f62\:5f0f\:7528\:6a21\:5f0f\:5339\:914d \:ff1a {Method,{integrand,integration variable},{transformed form}}*)
{intSubFra,{Cos[x^(1/2)],x},{2 y_ Cos[y_],y_,Sqrt[x]}},
{intSubFra,{x (x+1)^(1/2),x},{2 y_^2 (-1+y_^2),y_,Sqrt[1+x]}},
{intSubFra,{1/(x^(1/2)-x^(1/3)),x},{(6 y_^3)/(-1+y_),y_,x^(1/6)}},
{intSubFra,{((x+1)/(2x+3))^(1/2),x},{(2 y_^2)/(1-2 y_^2)^2,y_,Sqrt[(1+x)/(3+2 x)]}},
{intSubFra,{Sin[x],x},"NotMatch"},
{intSubPow,{x^3Sin[x^2],x},{1/2 y_ Sin[y_],y_,x^2}},
{intSubPow,{x^7/(x^12+1),x},{y_/(4 (1+y_^3)),y_,x^4}},
{intSubRfs,{ArcTan[y],y},{-(y_/(1+y_^2)),y_,y_,y_ ArcTan[y_]}}
};


(*Test Function*)
AutoTest[AL_]:=Module[
	{},
	Do[
		Print["Apply "<>ToString[AL[[i]][[1]]]<>" to "<>ToString[Level[AL[[i]][[2]],{1}],StandardForm]]; 
		If[MatchQ[Level[AL[[i]][[2]],{1},AL[[i]][[1]]],AL[[i]][[3]]],
			Print["Pass"],Print["Fail"]
	],
	{i,Length[AL]}
	]
]


AutoTest[AL]






