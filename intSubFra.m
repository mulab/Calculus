(* ::Package:: *)

(*If f has the form a*x+b,a and b are constants,this function returns the coefficients,otherwise returns Null*)
linear[f_,x_,a_,b_]:=Module[
	{m=a,n=b,temp},
	Switch[f,
	_Plus,(*the form is m*x+n*)
	If[!FreeQ[temp=Level[f,1][[1]],x],(*temp=m*x*)
		If[m=!=Null,
			If[m=!=temp/x||n=!=f-temp,
				Return[]
			],
			m=temp/x;
			If[!FreeQ[m,x],
				Return[]
			];
			n=f-temp;
			If[!FreeQ[n,x],
				Return[]
			]
		],
		(*temp=n*)
		If[m=!=Null,
			If[n=!=temp||m=!=(f-temp)/x,
				Return[]
			],
			n=temp;
			m=(f-temp)/x;
			If[!FreeQ[m,x],
				Return[]
			]
		]
	];
	Return[{m,n}],
	_,(*the form is m*x or x*)
	If[n=!=Null,
		If[n=!=0||m=!=f/x,
			Return[]
		],
		n=0
	];
	m=f/x;
	If[!FreeQ[m,x],
		Return[]
	];
	Return[{m,n}]
	]	
]


(*The integrand is of the form Elem (x,((a*x+b)/(c*x+d))^(Subscript[n, 1]/Subscript[m, 1]),((a*x+b)/(c*x+d))^(Subscript[n, 2]/Subscript[m, 2]),...),
where the Subscript[n, i] and Subscript[m, i] are relatively prime integers with some |Subscript[m, i]|!=1,and with a,b,c,d constants and ad-bc!=0.
substitute y=((a*x+b)/(c*x+d))^(1/k),k=least common multiple of the Subscript[m, i],returns the transformed integrand*)
intSubFra[f_,x_]:=Module[
	{e=f,pos=Position[f,Power[a_,_]/;!FreeQ[a,x]],a=Null,b=Null,c=Null,d=Null,m={},n={},loc={},i,loci,fra,base,exponent,deno,nume,temp,k,y},
	If[pos==={},Return["NotMatch"]];
	Do[
		loci=pos[[i]];
		If[loci!={},(*Extract cannot make sense at the root*)
			fra=Extract[e,loci],
			fra=e
		];
		base=Level[fra,1][[1]];
		exponent=Level[fra,1][[2]];
		If[FreeQ[base,x]||exponent==-1,
			Continue[]
		];
		If[Head[exponent]=!=Rational,
			Return["NotMatch"]
		];
		AppendTo[m,Denominator[exponent]];
		AppendTo[n,Numerator[exponent]];
		If[MatchQ[base,(a_ x+b_)/(c_ x+d_)]||MatchQ[base,(x+b_)/(c_ x+d_)]||MatchQ[base,x/(c_ x+d_)]
						||MatchQ[base,(a_ x+b_)/(x+d_)]||MatchQ[base,(x+b_)/(x+d_)]||MatchQ[base,x/(x+d_)]
								||MatchQ[base,(a_ x+b_)/x]||MatchQ[base,(x+b_)/x],
			If[Head[temp=Level[base,1][[1]]]===Power,
				deno=1/temp;
				nume=base*deno,
				nume=temp;
				deno=nume/base
			];
			If[linear[nume,x,a,b]=!=Null,
				{a,b}=linear[nume,x,a,b],
			];
			If[linear[deno,x,c,d]=!=Null,
				{c,d}=linear[deno,x,c,d]
			];
		];
		If[MatchQ[base,a_ x+b_]||MatchQ[base,x+b_]||MatchQ[base,x],
			If[linear[base,x,a,b]=!=Null,
				{a,b}=linear[base,x,a,b];
				{c,d}={0,1}
			]
		];
		If[MatchQ[base,1/(c_ x+d_)]||MatchQ[base,1/(x+d_)]||MatchQ[base,1/x],
			If[linear[1/base,x,c,d]=!=Null,
				{c,d}=linear[1/base,x,c,d];
				{a,b}={0,1}
			]
		];
		If[a===Null,(*None matches*)
			Return["NotMatch"]
		]
		If[a*d-b*c==0,
			Return["NotMatch"]
		];
		AppendTo[loc,loci],
		{i,Length[pos]}
	];
	If[m==={},Return["NotMatch"]];
	k=Apply[LCM,m];
	(*e=ReplacePart[e,loc->y];   Just substitute all x to y*)
	e=e*(k*(c*x+d)^2/(a*d-b*c)*((c*x+d)/(a*x+b))^(1/k-1));
	e=e/.x->(d*y^k-b)/(a-c*y^k);	
	Return[{Simplify[e,y>0],y,((a*x+b)/(c*x+d))^(1/k)}]                                     (*\:9ed8\:8ba4y>0\:53ef\:4ee5\:5417\:ff1f*)
]


(*Test:
intSubFra[Cos[x^(1/2)],x]
intSubFra[x (x+1)^(1/2),x]
intSubFra[1/(x^(1/2)-x^(1/3)),x]
intSubFra[((x+1)/(2x+3))^(1/2),x]
*)
