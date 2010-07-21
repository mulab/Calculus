(* ::Package:: *)

(*If f has the form a*x+b,a and b are constants,this function returns the coefficients,otherwise returns Null*)
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


(*The integrand is an elementary function of the trigonometric function applied to linear argument in the variable of integration.*)
intSubTri[f_,x_]:=Catch[
	Module[
	{e=f,pos,loci,triArg,triFun={{},{},{},{},{},{}},a=Null,b=Null,n,temp,s,trigList,i,y,t},
	tri={Sin,Cos,Tan,Cot,Sec,Csc};
	Do[
		pos=Position[e,tri[[k]][_]];(*gives the position of Trig (ax+b)*)
		(*Is the pattern of Trig (ax+b)*)
		Do[
			loci=pos[[i]];
			triArg=Extract[e,Append[loci,1]];(*triArg=a*x+b*)
			If[!FreeQ[triArg,x],
				If[linear[triArg,x,a,b]=!=Null,
					{a,b}=linear[triArg,x,a,b];
					AppendTo[triFun[[k]],loci],
					Throw["NotMatch"]
				]
			],
			{i,Length[pos]}
		];
		e=ReplacePart[e,triFun[[k]]->tri[[k]][t]],(*substitute Trig (ax+b) to Trig (t)*)
		{k,Length[tri]}
	];
	If[triFun[[1]]=={}&&triFun[[2]]=={},
		Throw["NotMatch"]
	];                                                           (*\:6743\:5b9c\:4e4b\:7b56\:ff0c\:6b64\:65b9\:6cd5\:4ee5\:540e\:5c1a\:9700\:5927\:7684\:6539\:8fdb*)
	(*Now has got all the trig information of f*)
	(*transform all trigonometric functions into sines and cosines,not done...*)

	(*transform the form Sin[x]^m*Cos[x]^n:NEEDED?*)
	
	(*cases that can substitute z=cosy or z=siny*)
	If[Head[e]===Times,
		temp=Part[e,1];
		trigList={Sin,Cos};
		For[i=1,i<3,i++,
		If[MatchQ[temp,trigList[[i]][t]^_Integer] && OddQ[Part[temp,2]],
			n=(Part[temp,2]-1)/2;
			temp=e/temp,
			If[MatchQ[e/temp,trigList[[i]][t]^Integer] && OddQ[Part[e/temp,2]],
				n=(Part[e/temp,2]-1)/2,
				If[MatchQ[temp,trigList[[i]][t]],
					n=0;
					temp=e/temp,
					If[MatchQ[e/temp,trigList[[i]][t]],
						n=0,
						Continue[]
					]
				]
			]
		];(*now temp is Elem (sint^2,cost) or Elem (cost^2,sint)*)
		pos=Position[temp,trigList[[i]][t]];
		Do[
			loci=pos[[i]];
			If[Head[s=Extract[temp,Delete[loci,-1]]]===Power&&Part[s,2]===2,
				temp=ReplacePart[temp,Delete[loci,-1]->1-y^2]
			],
			{i,Length[pos]}
		];
		If[i==1,
			temp=ReplacePart[temp,Position[temp,Cos[t]]->y];
			Throw[{-(1-y^2)^n*temp/a,y,y}],                                    (*\:6b64\:5904\:5047\:5b9a\:8fd4\:56de\:4ecd\:4e3ay,\:53ea\:4e3a\:8c03\:8bd5*)
			temp=ReplacePart[temp,Position[temp,Sin[t]]->y];
			Throw[{(1-y^2)^n*temp/a,y,y}]                                       (*\:540c\:4e0a*)
		]
		](*For cycle end*)
	];

	(*Cases that can substitute z=tany*)
	If[triFun[[1]]=={}&&triFun[[2]]=={}&&triFun[[4]]=={}&&triFun[[6]]=={},(*to transform to Elem (tant,sec^2 t   and temp=f*)
		temp=e;
		pos=Position[temp,Sec[t]];
		Do[
			loci=pos[[i]];
			If[Head[s=Extract[temp,Delete[loci,-1]]]===Power&&Part[s,2]===2,
				temp=ReplacePart[temp,Delete[loci,-1]->1+y^2]
			],
			{i,Length[pos]}
		];
		temp=ReplacePart[temp,Position[temp,Tan[t]]->y];
		Throw[{1/(1+y^2)*temp/a,y,y}];                                            (*\:540c\:4e0a*)
	];
	(*substitute z=tan1/2*y*)		
	If[triFun[[1]]=!={},e=ReplacePart[e,triFun[[1]]->2y/(1+y^2)]];
	If[triFun[[2]]=!={},e=ReplacePart[e,triFun[[2]]->(1-y^2)/(1+y^2)]];
	If[triFun[[3]]=!={},e=ReplacePart[e,triFun[[3]]->2y/(1-y^2)]];
	If[triFun[[4]]=!={},e=ReplacePart[e,triFun[[4]]->(1-y^2)/(2y)]];
	If[triFun[[5]]=!={},e=ReplacePart[e,triFun[[5]]->(1+y^2)/(1-y^2)]];
	If[triFun[[6]]=!={},e=ReplacePart[e,triFun[[6]]->(1+y^2)/(2y)]];
	Throw[{Simplify[2/(1+y^2)*e/a],y,y}];                                                (*\:540c\:4e0a*)

	Throw["NotMatch"](*!!Need improve,return transformed expressions,so are the aboves*)

]
]
	





