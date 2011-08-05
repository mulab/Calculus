(* ::Package:: *)

(* Mathematica Raw Program *)
IntegrateU[f_,x_]:=Module[
	{e=f,ans},
	ans=Calculus`Rubi`Int[e,x];
	If[!FreeQ[ans,Calculus`Rubi`Int],
		Print["Rubi Failed!"];
		ans=Calculus`Albi`Risch`pmint[e,x]
	];
	If[StringMatchQ[ToString[ans],"*Calculus`Albi`Risch*"],
		Print["Albi Failed!"];
		$Failed,
		Return[ans]
	];
]
