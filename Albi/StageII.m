(* ::Package:: *)

times=0;
ans=Null;
rfs=Null;
StageII[f_,x_]:=Module[
	{tans,xt=x},
	SetDirectory[NotebookDirectory[]];(*Set Package Diretory*)
	
	(*Import["intSubExp.m"];
	Import["intSubPow.m"];
	Import["intSubFra.m"];
	Import["intSubBin.m"];
	Import["intSubSqt.m"];
	Import["intSubTri.m"];
	Import["intSubRat.m"];
	Import["intSubRfs.m"];
	Import["intSubLog.m"];
	Import["IntTable.m"];
	Import["RationalQ.m"];

	If[(SubAns=intSubExp[f,x])=!="NotMatch",
		f=SubAns[[1]];x=ans[[2]];xt=x/.ans[[3]];
		If[(MainAnsExp=Main[f,x])=!="NotMatch",
			Return[{MainAnsExp/.x->xt}];
		];
	];
			
	Print[{"Now,f=",f,", x=",x,", xt=",xt}];*)
	Return["NotMatch"];
]


(*StageII[Exp[x]/(2+3Exp[2x]),x]*)


(*Elem (ai^(bi*xi+ci))*)
modExp[f_,x_]:=Module[
	{intinf,tans},(*intinf\:8bb0\:5f55\:79ef\:5206\:51fd\:6570\:4fe1\:606f*)
	If[(intinf=intSubExp[f,x,xt])=!="NotMatch",(*\:53ef\:4ee5\:8f6c\:6362*)
Print[{"exp",f,intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",(*\:67e5\:5230\:79ef\:5206\:8868*)
			ans=tans,
			If[RationalQ[intinf[[1]],intinf[[2]]],(*\:672a\:67e5\:5230\:79ef\:5206\:8868*)
				modRat[intinf[[1]],intinf[[2]]],(*\:8c03\:7528\:6709\:7406\:51fd\:6570\:6a21\:5757*)
				modTri[intinf[[1]],intinf[[2]]](*\:80fd\:8f6c\:6362\:ff0c\:8f6c\:6362\:540e\:975e\:6709\:7406\:51fd\:6570*)
			]
		],
		modPow[f,x](*\:4e0d\:80fd\:8f6c\:6362\:ff0c\:76f4\:63a5\:8c03\:7528\:4e0b\:4e00\:6a21\:5757*)
	]
]
(*Note:\:8f6c\:6362\:4e4b\:540e\:82e5\:975e\:6709\:7406\:51fd\:6570\:ff0c\:5219\:53ea\:80fd\:4e3a\:4e09\:89d2\:3001\:53cd\:4e09\:89d2\:53ca\:5bf9\:6570\:5f62\:5f0f*)	


(*x^c*Elem (x^ki)*)
modPow[f_,x_]:=Module[
	{intinf,tans},
	If[(intinf=intSubPow[f,x])=!="NotMatch",
Print[{"pow",f,intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
		ans=tans,
			If[RationalQ[intinf[[1]],intinf[[2]]],
				modRat[intinf[[1]],intinf[[2]]],
				modTri[intinf[[1]],intinf[[2]]]
			]
		],
		modFra[f,x]
	]
]


(*Elem (x,((a*x+b)/(c*x+d))^(ni/mi)*)
modFra[f_,x_]:=Module[
	{intinf,tans},
	If[(intinf=intSubFra[f,x])=!="NotMatch",
Print[{"fra",f,intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
		ans=tans,
			If[RationalQ[intinf[[1]],intinf[[2]]],
				modRat[intinf[[1]],intinf[[2]]],
				modTri[intinf[[1]],intinf[[2]]]
			]
		],
		modBin[f,x]
	]
]


(*A*x^r*(c1+c2*x^q)^p*)
modBin[f_,x_]:=Module[
	{intinf,tans},
	If[(intinf=intSubBin[f,x])=!="NotMatch",
Print[{"bin",f,intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
		ans=tans,
			If[RationalQ[intinf[[1]],intinf[[2]]],
				modRat[intinf[[1]],intinf[[2]]]
				(*\:8f6c\:6362\:4e4b\:540e\:5fc5\:4e3a\:6709\:7406\:51fd\:6570*)
			]
		],
		modSqt[f,x]
	]
]


(*R (x,Sqrt[c*x^2+b*x+a])*)
modSqt[f_,x_]:=Module[
	{intinf,tans},
	If[(intinf=intSubSqt[f,x])=!="NotMatch",
Print[{"sqt",f,intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
		ans=tans,
		modTri[intinf[[1]],intinf[[2]]]
		(*\:8f6c\:6362\:4e4b\:540e\:5fc5\:4e3a\:4e09\:89d2\:51fd\:6570*)
		],
		modTri[f,x]
	]
]


(*TRIG (a+b*x)*)
modTri[f_,x_]:=Module[
	{intinf,tans},
	If[(intinf=intSubTri[f,x])=!="NotMatch",
Print[{"tri",f,intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
			ans=tans,
			If[RationalQ[intinf[[1]],intinf[[2]]],
				modRat[intinf[[1]],intinf[[2]]],
				modRfs[intinf[[1]],intinf[[2]]](*\:8df3\:8fc7Method7*)
			]
		],
		modRfs[f,x](*\:8df3\:8fc7Method7*)
	]
]	


(*R (x)*e^P(x)*)
(*
modRte[f_,x_]:=Module[
	{intinf,tans},
	expr
]
*)


(*Rational functions*)
modRat[f_,x_]:=Module[
	{intinf,tans},
	If[(tans=IntTable[f,x])=!="NotFound",
		ans=tans,(*\:67e5\:5230\:79ef\:5206\:8868*)
		ans=intSubRat[f,x](*\:6709\:7406\:51fd\:6570\:79ef\:5206\:65b9\:6cd5*)
	]
]


(*R (x)F (S (x)) where F is log,arcsin,or arctan*)
modRfs[f_,x_]:=Module[
	{intinf,tans},
	If[(intinf=intSubRfs[f,x])=!="NotMatch",(*intSubRfs\:8f6c\:6362\:8fd4\:56de\:7ed3\:679c\:4e3a\:4e09\:9879\:7684\:8868\:ff0c\:524d\:4e24\:9879\:76f8\:540c\:ff0c\:540e\:4e00\:9879\:4e3a\:5206\:90e8\:79ef\:5206\:7684\:4e58\:79ef\:9879*)
Print[{"rfs",f,intinf}];
		rfs=intinf[[3]];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
			ans=tans,
			If[RationalQ[intinf[[1]],intinf[[2]]],
				modRat[intinf[[1]],intinf[[2]]],
				modLog[intinf[[1]],intinf[[2]]]
			]
		],
		modLog[f,x]
	]			
]


(*R (x)Elem (Log[c,a+b*x])*)
modLog[f_,x_]:=Module[
	{intinf,tans},
	If[(intinf=intSubLog[f,x])=!="NotMatch",
Print[{"log",f,intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
			ans=tans,
			If[RationalQ[intinf[[1]],intinf[[2]]],
				modRat[intinf[[1]],intinf[[2]]],
Print[times];
				times+=1;(*\:9650\:5236\:6b21\:6570\:ff0c\:9632\:6b62\:6b7b\:5faa\:73af*)
				If[times==3,
					Throw[Integrate[intinf[[1]],intinf[[2]]]
				]
				modPow[ExpandAll[intinf[[1]]],intinf[[2]]]                          (**)
			]
		],
		modPow[ExpandAll[f],x]]
	]
]



(*stageII[Sin[x],x]
stageII[E^(2 x)/(a + b E^(4 x)), x]
stageII[x^3Sin[x^2],x]
stageII[x^7/(x^12+1),x]
stageII[Cos[x^(1/2)],x]
stageII[1/(x^(1/2)-x^(1/3)),x]
stageII[x^(1/2)*(1+x)^(5/2),x]
stageII[Sqrt[A^2+B^2*Cos[2x]^2]*Cos[2x],x]
stageII[Sqrt[1-4x+3x^2]/(1+x^2),x]
stageII[y^2* ArcTan[y],y]
stageII[1/(x (1+(Log[x])^2)),x]
*)
