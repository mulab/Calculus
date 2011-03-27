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


(*The integrand is an elementary function of the trigonometric function applied to linear argument in the variable of integration.*)
intSubTri[f_,x_]:=Catch[
	Module[
	{e=f,pos,loci,triArg,triFun={{},{},{},{},{},{}},a=Null,b=Null,t,et,temp,i,j,k,trigList,s,n,sin,cos,tan,sec,y},
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
	
	(*All trigonometric functions transformed into sines and cosines*)
	et=ReplacePart[e,{triFun[[1]]->sin,triFun[[2]]->cos,triFun[[3]]->sin/cos,triFun[[4]]->cos/sin,triFun[[5]]->1/cos,triFun[[6]]->1/sin}];
	
	If[Head[et]===Times,
		parts=Level[et,1];
		trigList={sin,cos};
		For[j=1,j<=Length[parts],j++,(*outer for cycle*)
			temp=Part[et,j];	
			For[i=1,i<=Length[trigList],i++,(*inner for cycle*)
				If[MatchQ[temp,trigList[[i]]^_Integer] && OddQ[Part[temp,2]],
					n=(Part[temp,2]-1)/2;
					temp=et/temp,
					If[MatchQ[temp,trigList[[i]]],
						n=0;
						temp=et/temp,
						Continue[](*next inner for cycle step*)
					]
				];
				(*now temp is supposed to be Elem (sint^2,cost) or Elem (cost^2,sint)*)
				pos=Position[temp,trigList[[i]]];
				If[Catch[
					Do[
						loci=pos[[k]];
						If[Head[s=Extract[temp,Delete[loci,-1]]]===Power&&Part[s,2]===2,
							temp=ReplacePart[temp,Delete[loci,-1]->1-y^2],
							Throw["break"]
						],
						{k,Length[pos]}
					]
					]==="break",
					Break[];(*inner for cycle break*)
				]

				If[i==1,
					temp=ReplacePart[temp,Position[temp,cos]->y];
					Throw[{-(1-y^2)^n*temp/a,y,Cos[a*x+b]}],
					temp=ReplacePart[temp,Position[temp,sin]->y];
					Throw[{(1-y^2)^n*temp/a,y,Sin[a*x+b]}]
				]
			](*inner for cycle end*)
		](*outer for cycle end*)
	];

	(*All trigonometric functions transformed into secants and tangents*)
	et=ReplacePart[e,{triFun[[1]]->tan/sec,triFun[[2]]->1/sec,triFun[[3]]->tan,triFun[[4]]->1/tan,triFun[[5]]->sec,triFun[[6]]->sec/tan}];
	pos=Position[et,sec];
	If[Catch[
		Do[
			loci=pos[[k]];
			If[Head[s=Extract[et,Delete[loci,-1]]]===Power&&Part[s,2]===2,(*Of the form Elem (tant,sect^2)*)
				et=ReplacePart[et,Delete[loci,-1]->1+y^2],
				Throw["break"]
			],
			{k,Length[pos]}
		]
		]=!="break",
		et=ReplacePart[et,Position[et,tan]->y];
		Throw[{1/(1+y^2)*et/a,y,Tan[a*x+b]}]
	];
	(*substitute z=tan1/2*y*)
	et=ReplacePart[e,{triFun[[1]]->2y/(1+y^2),triFun[[2]]->(1-y^2)/(1+y^2),triFun[[3]]->2y/(1-y^2),triFun[[4]]->(1-y^2)/(2y),triFun[[5]]->(1+y^2)/(1-y^2),triFun[[6]]->(1+y^2)/(2y)}];
	Throw[{Simplify[2/(1+y^2)*et/a],y,Tan[1/2*(a*x+b)]}];
	Throw["NotMatch"]
	]
]	


(*Examples
intSubTri[Sin[t+r x]*Tan[r x+t],x]
intSubTri[(Sin[t+r x])*Tan[r x+t]/(1+Cot[r x+t]/Csc[r x+t]),x]
intSubTri[(Sin[t+r x])^2*Tan[r x+t]/(1+Cot[r x+t]/Csc[r x+t]),x]
intSubTri[(1+Tan[t+r x])*(Sec[t+r x])^2,x]
*)



(* ::InheritFromParent:: *)
(**)
