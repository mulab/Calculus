(* ::Package:: *)

(*gives the indefinite integral of \[Integral]op (f (x))*f'(x)\[DifferentialD]x by searching the integral table*)
inTable[opf_,f_,x_]:=Module[
	{},
	Return[Integrate[opf*D[f,x],x]]
];


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
intDDM[f_,x_]:=Module[
	{e=f,c=1,i,u,v,ans=Null},
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
				ans=c*v/D[u,x]*inTable[e[[i]],u,x];
				Break[]
			],
			{i,Length[e]}
		];(*enumerates the op (f (x)) part*)
		If[ans=!=Null,
			Return[ans]
		],
		u=separate[e,1,x];
		If[u=!=Null,
			Return[c/D[u,x]*inTable[e,u,x]]
		]
	];

	Return[A[f,x]]
];


(*intDDM[x E^x^2,x]
intDDM[4Cos[2x+3] ,x]
intDDM[E^x/(1+E^x),x]
intDDM[Sin[x]Cos[x],x]
intDDM[x (x^2+1)^(1/2),x]
intDDM[Cos[E^x]^2 Sin[E^x] E^x,x]*)
