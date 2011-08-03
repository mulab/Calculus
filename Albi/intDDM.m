(* ::Package:: *)

op={Sin,Cos,Tan,Cot,Sec,Csc,ArcSin,ArcTan,ArcSec,Log};
(*determines whether f is of the form op (u) where u'=v, and returns u*)
separate[f_,v_,x_]:=Module[
	{i,ans=Null},
	If[f==0,
		Return[]
	];
	If[FreeQ[v/D[f,x],x],
		Return[f]
	];(*f=u, v=f'*)
	If[Head[f]===Power&&FreeQ[f[[2]],x]&&FreeQ[v/D[f[[1]],x],x],
		Return[f[[1]]]
	];(*f=u^const*)
	If[Head[f]===Power&&FreeQ[f[[1]],x]&&FreeQ[v/D[f[[2]],x],x],
		Return[f[[2]]]
	];(*f=const^u*)
	Do[
		If[Head[f]===op[[i]]&&FreeQ[v/D[f[[1]],x],x],
			ans=f[[1]];
			Break[]
		],
		{i,Length[op]}
	];(*f=op (u)*)
	Return[ans]
];


(*gives the indefinite integral of \[Integral]f \[DifferentialD]x by derivative-divides method*)
(*Note: this is a rule, not return Integration*)
(*Shao Qiming*)
intDDM[f_,x_]:=Catch[Module[
	{e=f,c=1,i,u,v},
	If[Head[e]===Times,
		Do[
			If[FreeQ[e[[i]],x],
				c=c*e[[i]]
			],
			{i,Length[e]}
		]
	];(*gets the constant coefficient of the integrand*)
	e=e/c;(*eliminates the constant coefficient*)

	If[Head[e]===Times,
		Do[
			v=e/e[[i]];
			u=separate[e[[i]],v,x];
			If[u=!=Null,
				(*ans=c*v/D[u,x]*inTable[e[[i]],u,x];*)
				e=e/D[u,x];
				e=e/.u->y;
				Throw[{c*e,y,u}]
			],
			{i,Length[e]}
		],(*enumerates the op (f (x)) part*)
		u=separate[e,1,x];
		If[u=!=Null,
				e=e/D[u,x];
				e=e/.u->y;
				Throw[{c*e,y,u}];
		]
	];
	Return["NotMatch"]
]
]


(*
intDDM[x E^x^2,x]
intDDM[4Cos[2x+3] ,x]
intDDM[E^x/(1+E^x),x]
intDDM[Sin[x]Cos[x],x]
intDDM[x (x^2+1)^(1/2),x]
intDDM[Cos[E^x]^2 Sin[E^x] E^x,x]
intDDM[x^2,x](*\:3002\:3002\:3002\:3002Anything is converted*)
intDDM[Cos[x]^2 Sin[x],x]

*)



