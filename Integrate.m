(* ::Package:: *)

RubiNotLoaded = True

(* Mathematica Raw Program *)
IntegrateU[f_,x_]:=Module[
	{e=f,ans},

	If[RubiNotLoaded,
		Get[Calculus`CWD <> "Rubi/init.m"];
		RubiNotLoaded = False
	];
	ans = Calculus`Rubi`Int[e,x];

	If[FreeQ[ans,Calculus`Rubi`Int], Return[ans],
		Print["Rubi Failed!"];
		Return[$Failed]
	]
]
