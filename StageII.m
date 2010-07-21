(* ::Package:: *)

stageII[f_,x_]:=Catch[Module[
	{tans},
	ans=Null;
	rfs=0;(*used for integration by parts*)
	times=0;
	intinf={};(*record the infomation of a function to integrate*)
	tans;(*template answer*)
	SetDirectory[NotebookDirectory[]];(*set directory to current directory*)
	Import["intSubExp.m"];
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
	If[(tans=IntTable[f,x])=!="NotFound",
		ans=tans,
		modPow[{f,x,x}]                        (*\:6682\:65f6\:4eceModPow \:5f00\:59cb *)
	];
	If[rfs=!=0,
		ans +=rfs
	];(*\:5206\:90e8\:79ef\:5206*)
	Throw[ans]
]]


(*Elem (ai^(bi*xi+ci))*)
modExp[ii_]:=Module[
	{},
	If[(intinf=intSubExp[ii[[1]],ii[[2]]])=!="NotMatch",(*\:53ef\:4ee5\:8f6c\:6362*)
		intinf[[3]]=intinf[[3]]/.ii[[2]]->ii[[3]];(*\:53d8\:91cf\:66ff\:6362\:8fd8\:539f*)
Print[{"exp",ii[[1]],intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",(*\:67e5\:5230\:79ef\:5206\:8868*)
			ans=tans/.intinf[[2]]->intinf[[3]],
			If[RationalQ[intinf[[1]],{intinf[[2]]}],(*\:672a\:67e5\:5230\:79ef\:5206\:8868*)
				modRat[intinf],(*\:8c03\:7528\:6709\:7406\:51fd\:6570\:6a21\:5757*)
				modTri[intinf](*\:80fd\:8f6c\:6362\:ff0c\:8f6c\:6362\:540e\:975e\:6709\:7406\:51fd\:6570*)
			]
		],
		modPow[ii](*\:4e0d\:80fd\:8f6c\:6362\:ff0c\:76f4\:63a5\:8c03\:7528\:4e0b\:4e00\:6a21\:5757*)
	]
]
(*Note:\:8f6c\:6362\:4e4b\:540e\:82e5\:975e\:6709\:7406\:51fd\:6570\:ff0c\:5219\:53ea\:80fd\:4e3a\:4e09\:89d2\:3001\:53cd\:4e09\:89d2\:53ca\:5bf9\:6570\:5f62\:5f0f *)	


(*x^c*Elem (x^ki)*)
modPow[ii_]:=Module[
	{},
	If[(intinf=intSubPow[ii[[1]],ii[[2]]])=!="NotMatch",
		intinf[[3]]=intinf[[3]]/.ii[[2]]->ii[[3]];
Print[{"pow",ii[[1]],intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
			ans=tans/.intinf[[2]]->intinf[[3]],
			If[RationalQ[intinf[[1]],{intinf[[2]]}],
				modRat[intinf],
				modTri[intinf]
			]
		],
		modFra[ii]
	]
]


(*Elem (x,((a*x+b)/(c*x+d))^(ni/mi)*)
modFra[ii_]:=Module[
	{},
	If[(intinf=intSubFra[ii[[1]],ii[[2]]])=!="NotMatch",
		intinf[[3]]=intinf[[3]]/.ii[[2]]->ii[[3]];
Print[{"fra",ii[[1]],intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
			ans=tans/.intinf[[2]]->intinf[[3]],
			If[RationalQ[intinf[[1]],{intinf[[2]]}],
				modRat[intinf],
				modTri[intinf]
			]
		],
		modBin[ii]
	]
]


(*A*x^r*(c1+c2*x^q)^p*)
modBin[ii_]:=Module[
	{},
	If[(intinf=intSubBin[ii[[1]],ii[[2]]])=!="NotMatch",
		intinf[[3]]=intinf[[3]]/.ii[[2]]->ii[[3]];
Print[{"bin",ii[[1]],intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
		ans=tans/.intinf[[2]]->intinf[[3]],
		modRat[intinf]
		(*\:8f6c\:6362\:4e4b\:540e\:5fc5\:4e3a\:6709\:7406\:51fd\:6570*)
		],
		modSqt[ii]
	]
]


(*R (x,Sqrt[c*x^2+b*x+a])*)
modSqt[ii_]:=Module[
	{},
	If[(intinf=intSubSqt[ii[[1]],ii[[2]]])=!="NotMatch",
		intinf[[3]]=intinf[[3]]/.ii[[2]]->ii[[3]];
Print[{"sqt",ii[[1]],intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
		ans=tans/.intinf[[2]]->intinf[[3]],
		modTri[intinf]
		(*\:8f6c\:6362\:4e4b\:540e\:5fc5\:4e3a\:4e09\:89d2\:51fd\:6570*)
		],
		modTri[ii]
	]
]


(*TRIG (a+b*x)*)
modTri[ii_]:=Module[
	{},
	If[(intinf=intSubTri[ii[[1]],ii[[2]]])=!="NotMatch",
		intinf[[3]]=intinf[[3]]/.ii[[2]]->ii[[3]];
Print[{"tri",ii[[1]],intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
			ans=tans/.intinf[[2]]->intinf[[3]],
			If[RationalQ[intinf[[1]],{intinf[[2]]}],
				modRat[intinf],
				modRfs[intinf](*\:8df3\:8fc7Method7*)
			]
		],
		If[RationalQ[ii[[1]],{ii[[2]]}],
		modRat[ii],
		modRfs[ii](*\:8df3\:8fc7Method7*)
		]
	]
]	


(*R (x)*e^P(x)*)
(*
modRte[ii_]:=Module[
	{},
	expr
]
*)


(*Rational functions*)
modRat[ii_]:=Module[
	{},
	(*\:4e0d\:5fc5\:518d\:67e5\:79ef\:5206\:8868\:4e86*)
Print[{"rat",ii}];
	ans=intSubRat[ii[[1]],ii[[2]]]/.ii[[2]]->ii[[3]](*\:6709\:7406\:51fd\:6570\:79ef\:5206\:65b9\:6cd5*)
]


(*R (x)F (S (x)) where F is log,arcsin,or arctan*)
modRfs[ii_]:=Module[
	{},
	If[(intinf=intSubRfs[ii[[1]],ii[[2]]])=!="NotMatch",(*intSubRfs\:8f6c\:6362\:8fd4\:56de\:7ed3\:679c\:4e3a\:56db\:9879\:7684\:8868\:ff0c\:524d\:4e09\:9879\:76f8\:540c\:ff0c\:540e\:4e00\:9879\:4e3a\:5206\:90e8\:79ef\:5206\:7684\:4e58\:79ef\:9879*)
		intinf[[3]]=intinf[[3]]/.ii[[2]]->ii[[3]];
Print[{"rfs",ii[[1]],intinf}];
		rfs += intinf[[4]]/.intinf[[2]]->intinf[[3]];(*\:6709\:53ef\:80fd\:591a\:6b21\:5206\:90e8\:79ef\:5206\:ff0c\:6545\:7528 +=*)
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
			ans=tans/.intinf[[2]]->intinf[[3]],
			If[RationalQ[intinf[[1]],{intinf[[2]]}],
				modRat[intinf],
				modLog[intinf]
			]
		],
		modLog[ii]
	]			
]


(*R (x)Elem (Log[c,a+b*x])*)
modLog[ii_]:=Module[
	{},
	times+=1;
Print["times=",times];
	If[times==3,(*\:9650\:5236\:6b21\:6570\:ff0c\:9632\:6b62\:6b7b\:5faa\:73af*)
Print[{"times to 3",ii}];
		Throw["Sorry,we did our best effort but still cannot deal with it...orz"]
	];
	If[(intinf=intSubLog[ii[[1]],ii[[2]]])=!="NotMatch",
		intinf[[3]]=intinf[[3]]/.ii[[2]]->ii[[3]];
Print[{"log",ii[[1]],intinf}];
		If[(tans=IntTable[intinf[[1]],intinf[[2]]])=!="NotFound",
			ans=tans/.intinf[[2]]->intinf[[3]],
			If[RationalQ[intinf[[1]],{intinf[[2]]}],
				modRat[intinf],
				intinf[[1]]=ExpandAll[intinf[[1]]];(*\:5c55\:5f00\:88ab\:79ef\:51fd\:6570*)
				modPow[intinf]                          (*\:6682\:65f6\:4eceModPow \:5f00\:59cb *)
			]
		],
		ii[[1]]=ExpandAll[ii[[1]]];
		modPow[ii]
	]
]






