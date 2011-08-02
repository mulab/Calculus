(* ::Package:: *)

(*\:5224\:65ad\:51fd\:6570\:662f\:5426\:4e3a\:6709\:7406\:5206\:5f0f*)
(*Shao Qiming & Zhang Junlin*)
(*\:672c\:7a0b\:5e8f\:8fd9\:4e48\:590d\:6742\:6ca1\:6709\:5fc5\:8981\:ff0c\:5229\:7528Coefficient\:ff0c\:53ef\:4ee5\:5feb\:901f\:5b9e\:73b0
\:53ef\:4ee5\:5206\:522b\:5224\:65ad\:5206\:5b50\:ff0c\:5206\:6bcd\:662f\:5426\:4e3a\:591a\:9879\:5f0f*)
(*RationalQ[f_,l_]:=Module[
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
]*)

(*\:4e0d\:7528\:5904\:7406\:5e26\:53c2\:6570\:7684\:6709\:7406\:5f0f*)
(*\:4e0d\:80fd\:5904\:7406\:4e24\:9879\:76f8\:52a0\:7684\:6709\:7406\:5f0f*)
RationalQ[f_,L_]:=Module[
{e=f,pos,i,temp,nume,deno,bo},
bo=True;
pos=Position[e,_Symbol];
Do[temp=Extract[e,pos[[i]]];If[temp=!=Plus&&temp=!=Times&&temp=!=Power&&temp=!=Rational&&FreeQ[L,temp],
	Return[False]],
	{i,Length[pos]}];(*\:8fd9\:4e00\:6b65\:7528\:6765\:6392\:9664Sin[]\:7b49\:5176\:5b83\:975e\:6709\:7406\:5f0f\:7684\:51fd\:6570\:ff0c\:4f46\:662f\:8be5\:6b65\:5728\:5904\:7406\:6709\:7406\:7cfb\:6570\:65f6\:5b58\:5728Bug*)
nume=Numerator[e];
deno=Denominator[e];
(*Print[{nume,deno}];*)
Do[
temp=L[[i]];
If[!PolynomialQ[nume,temp]||!PolynomialQ[deno,temp],bo=False],
{i,Length[L]}
];
Return[bo]
](*\:5173\:4e8eReturn\:5728\:51fd\:6570\:548cDo\:4e2d\:7684\:8fd0\:4f5c\:60c5\:51b5*)
(*\:5bf9\:6bd4Return[False]\:548cbo=False\:4e24\:79cd\:60c5\:51b5*)


(*RationalQ[x^2,{x}]
RationalQ[x^(1/2),{x}]
RationalQ[x^5+Sin[x] x^7,{x}]
RationalQ[(x^5+x^7+y^3)/(x^3+y^5),{x,y}]
RationalQ[4 x Log[x]+x+1,{x}]*)
