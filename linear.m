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
