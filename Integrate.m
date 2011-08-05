(* ::Package:: *)

(* Mathematica Raw Program *)
IntegrateU[f_,x_]:=Module[
	{e=f,ans},
	ans=Calculus`Rubi`Int[e,x];
	If[!FreeQ[ans,Calculus`Rubi`Int],ans=Calculus`Albi`Risch`pmint[e,x]];
	If[FreeQ[ans,Calculus`Albi`Risch`pmint],
		Return[ans],
		Return["IntegrateU["<>String[f]<>"]"]
	];
]
