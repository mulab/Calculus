(* ::Package:: *)

RationalQ[f_,l_]:=Module[
	{Free,i,Equ,able},
	Free=True;Equ=False;
	For[i=1,i<=Length[l],i++,If[!FreeQ[f,l[[i]]],Free=False]];
	If[Free,Return[True]];

	For[i=1,i<=Length[l],i++,If[f==l[[i]],Equ=True]];
	If[Equ,Return[True]];
	
	If[Head[f]==Plus,
		able=True;
		For[i=1,i<=Length[f],i++,If[!RationalQ[f[[i]],l],able=False]];
		If[able,Return[True],Return[False]]
	];
	(*Print[f," Plus done"];*)
	If[Head[f]==Minus,
		able=True;
		For[i=1,i<=Length[f],i++,If[!RationalQ[f[[i]],l],able=False]];
		If[able,Return[True],Return[False]]
	];
	(*Print[f," Minus done"];*)
	If[Head[f]==Times,
		able=True;
		For[i=1,i<=Length[f],i++,If[!RationalQ[f[[i]],l],able=False]];
		If[able,Return[True],Return[False]]
	];
	(*Print[f," Times done"];*)
	If[Head[f]==Rational,
		If[RationalQ[f[[1]],l]==True&&RationalQ[f[[2]],l]==True,Return[True],Return[False]];
	];
	(*Print[f," Rational done"];
	Print[R[f[[1]],l]];
	Print[IntegerQ[f[[2]]]];*)
	If[Head[f]==Power,
		If[RationalQ[f[[1]],l]==True && IntegerQ[f[[2]]],Return[True],Return[False]]
	];
	(*Print[f," Power done"];*)
	Return[False]
]


RationalQ[x^2,{x}]


RationalQ[x^(1/2),{x}]


RationalQ[x^5+Sin[x] x^7,{x}]


RationalQ[(x^5+x^7+y^3)/(x^3+y^5),{x,y}]


RationalQ[4 x Log[x]+x+1,{x}]


RationalQ[]


TreeForm[Log[x]]
