(* ::Package:: *)

(*If f has the form a*x+b,a and b are constants,
this function returns the coefficients,otherwise returns Null*)
linear[f_,x_,a_,b_]:=Module[
	{m=a,n=b,temp},
	Switch[f,
	_Plus,(*the form is m*x+n*)
	If[!FreeQ[temp=Level[f,1][[1]],x],(*temp=m*x*)
		If[m=!=Null,
			If[m!=temp/x||n!=f-temp,
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
			If[n!=temp||m!=(f-temp)/x,
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
		If[n!=0||m!=f/x,
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
(*\:4e0d\:7406\:89e3\:8be5\:51fd\:6570\:529f\:80fd\:ff0c\:5df2\:88ab\:4e0b\:9762\:7684Lin\:66ff\:4ee3*)


(*\:5982\:679c\:5185\:6838\:63d0\:4f9bCoefficientList\:51fd\:6570\:ff0c\:5219\:4e0d\:9700\:8981\:8be5Lin\:51fd\:6570*)
Lin[f_,x_]:=Module[
{m,n,temp,e=f},
If[MatchQ[e,a_ x +b_], m=e[[2,1]];n=e[[1]]];
If[MatchQ[e,x+b_],m=1;n=e[[1]]];
If[MatchQ[e,x],m=1;n=0];
If[MatchQ[e,a_ x],m=e[[1]];n=0];
If[FreeQ[e,x],m=0;n=e];
Return[{m,n}]
]


(*The integrand is of the form Elem (x,((a*x+b)/(c*x+d))^(Subscript[n, 1]/Subscript[m, 1]),((a*x+b)/(c*x+d))^(Subscript[n, 2]/Subscript[m, 2]),...),
where the Subscript[n, i] and Subscript[m, i] are relatively prime integers with some |Subscript[m, i]|!=1,and with a,b,c,d constants and ad-bc!=0.
substitute y=((a*x+b)/(c*x+d))^(1/k),k=least common multiple of the Subscript[m, i],returns the transformed integrand*)
(*the method 3 of SIN ( Symbolic INtegrator ) stage II*)
(*Shao Qiming & Zhang Junlin*)
intSubFra[f_,x_]:=Module[
	{e=f,y,pos=Position[f,Power[a_,_]/;!FreeQ[a,x]],a=Null,b=Null,c=Null,d=Null,m={},n={},loc={},i,loci,fra,base,exponent,deno,nume,temp,k},
	If[pos==={},Return["NotMatch"]];
	Do[
		loci=pos[[i]];
		If[loci!={},(*Extract cannot make sense at the root*)
			fra=Extract[e,loci],
			fra=e
		];(*f=((x+1)/(2 x +3))^(2/3) as example,,sqm*)
		base=Level[fra,1][[1]];
		exponent=Level[fra,1][[2]];
		If[FreeQ[base,x]||exponent==-1,
			Continue[]
		];(*f=1/(2 x +3) as example,,sqm*)
		If[Head[exponent]=!=Rational,
			Return["NotMatch"]
		];(*\:662f\:4e0d\:662f\:6709\:70b9\:6b66\:65ad,,sqm*)
		AppendTo[m,Denominator[exponent]];
		AppendTo[n,Numerator[exponent]];
		(*If[MatchQ[base,(a_ x+b_)/(c_ x+d_)]||MatchQ[base,(x+b_)/(c_ x+d_)]||MatchQ[base,x/(c_ x+d_)]
						||MatchQ[base,(a_ x+b_)/(x+d_)]||MatchQ[base,(x+b_)/(x+d_)]||MatchQ[base,x/(x+d_)]
								||MatchQ[base,(a_ x+b_)/x]||MatchQ[base,(x+b_)/x],(*then*)
(*			If[Head[temp=Level[base,1][[1]]]===Power,
				deno=1/temp;
				nume=base*deno,(*else*)
				nume=temp;
				deno=nume/base
			];*)

(*??\:8fd9\:662f\:9488\:5bf9\:4ec0\:4e48\:60c5\:51b5*)
(*			If[linear[nume,x,a,b]=!=Null,
				{a,b}=linear[nume,x,a,b]
			];
			If[linear[deno,x,c,d]=!=Null,
				{c,d}=linear[deno,x,c,d]
			](*\:4e0d\:80fd\:7406\:89e3linear\:51fd\:6570\:5230\:5e95\:662f\:5e72\:4ec0\:4e48\:7684\:ff0c\:7adf\:7136\:662f\:5bf9\:7684\:ff0c\:795e\:5947*)*)
			{a,b}=Lin[nume,x];
			{c,d}=Lin[deno,x]
		];
		If[MatchQ[base,a_ x+b_]||MatchQ[base,x+b_]||MatchQ[base,x],
(*			If[linear[base,x,a,b]=!=Null,
				{a,b}=linear[base,x,a,b];
				{c,d}={0,1}*)
			{a,b}=Lin[nume,x];
			{c,d}=Lin[deno,x]
			];
		If[MatchQ[base,1/(c_ x+d_)]||MatchQ[base,1/(x+d_)]||MatchQ[base,1/x],
(*			If[linear[1/base,x,c,d]=!=Null,*)
			{a,b}=Lin[nume,x];
			{c,d}=Lin[deno,x]
		];*)
(*If[MatchQ[base,(a_ x+b_)/(c_ x+d_)]||MatchQ[base,(x+b_)/(c_ x+d_)]||MatchQ[base,x/(c_ x+d_)]
						||MatchQ[base,(a_ x+b_)/(x+d_)]||MatchQ[base,(x+b_)/(x+d_)]||MatchQ[base,x/(x+d_)]
								||MatchQ[base,(a_ x+b_)/x]||MatchQ[base,(x+b_)/x]||MatchQ[],*)(*then*)
			nume=Numerator[base];
			deno=Denominator[base];
			{a,b}=Lin[nume,x];
			{c,d}=Lin[deno,x];
(*			Return["NotMatch"]
]*)
		(*Print[{a,b,c,d}];*)
		If[a===Null,(*None matches*)
			Return["NotMatch"]
		];
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
	Return[{Simplify[e,y>0],y,((a x+b)/(c x+d))^(1/k)}]                                     (*\:9ed8\:8ba4y>0\:53ef\:4ee5\:5417\:ff1f*)
	(*Shao Qiming\:6ce8\:ff1a\:73b0\:5728\:4e0d\:5224\:65ad\:6570\:7684\:7c7b\:578b\:ff0c\:4e00\:5f8b\:9ed8\:8ba4\:4e3a\:6b63\:6570*)
]


(*intSubFra[Cos[x^(1/2)],x]
intSubFra[x (x+1)^(1/2),x]
intSubFra[1/(x^(1/2)-x^(1/3)),x]
intSubFra[((x+1)/(2x+3))^(1/2),x]
intSubFra[Sin[x],x]
intSubFra[x^(2/3)/(x^(1/2)-x^(1/6)),x]
linear[3 x+ 5,x,c,d]
Lin[2 x+5,x]
Lin[1,x]*)



