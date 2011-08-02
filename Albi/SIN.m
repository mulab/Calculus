(* ::Package:: *)

Main[f_,x_]:=Module[
	{e=f,right,c=1,re},
	SetDirectory[NotebookDirectory[]];
(*	Import["StageII.m"];*)
	Import["..\\Rubi\\IntTable.m"];
	Import["..\\Rubi\\NoCloseTable.m"];
	Import["intDDM.m"];
	(*Is there any warning?*)
	(*Stage I Method I*)
	
	(*\:5173\:4e8e\:52a0\:6cd5\:7684\:90e8\:5206\:ff0c\:9700\:8981\:8003\:8651\:4e24\:9879\:6216\:8005\:4e09\:9879\:5408\:5e76\:8003\:8651\:7684\:5fc5\:8981*)
(*	If[ Head[e]==Plus,
		If[ (Main[e[[1]],x]=!="NotFound")&&(Main[e[[2]],x]=!="NotFound"),
			Return[Main[e[[1]],x]+Main[e[[2]],x]]
		]
	];*)
	If[Head[e]===Plus,Return[Main[e[[1]],x]+Main[e-e[[1]],x]]];

(*the head of e is impossible to be Minus*)
(*	If[ Head[e]==Minus,
		If[ (Main[e[[1]],x]=!="NotFound")&&(Main[e[[2]],x]=!="NotFound"),
			Return[Main[e[[1]],x]-Main[e[[2]],x]]
		]
	];*)
	(*Get Constant*)
	If[Head[e]===Times,
		Do[
			If[FreeQ[e[[i]],x],
				c=c*e[[i]]
			],
			{i,Length[e]}
		];
		Return[c*Main[e/c,x]];
	];
	 
(*	If[ Head[e]==Times,
		If[ (D[e[[1]],x]==0),
			Return[e[[1]]*Main[e[[2]],x]]
		];
		If[ (D[e[[2]],x]==0),
			Return[e[[2]]*Main[e[[1]],x]]
		];
	];*)
	
	(*\:7a81\:7136\:53d1\:73b0intDDM\:6709\:70b9\:4e07\:80fd\:ff0c\:6709\:70b9bug*)
	re=intDDM[e,x];
	rex=re/.re[[2]]->x;
	If[re=!="NotMatch"&&re=!=rex,Return[Main[ re[[1]],re[[2]] ]/.re[[2]]->re[[3]] ] ];
	
	(*Stage I Method II*)
	If[ Head[e]==Power,
		right=e[[2]];
		If[ (Head[right]===Integer&&right>0)&&(MatchQ[e[[1]],Plus[_,__]]),
			Return[Main[Expand[e],x]]			
		];
	];
	
	(*If[ IntDDM[e,x]=!="NotMatch",
		Return[IntDDM[e,x]]
	];*)
	
	(*Check the table*)
	
	If[IntTable[e,x]=!="NotFound",
		Return[IntTable[e,x]]
	];

	If[NoClose[e,x]==="NoClose",
		Return["NoClose"]
	];

	Return["NOW CANNOT BE SOLVED"]
	(*Return[StageII[e,x]]*)
];


(*Main[1,x]
Main[5/(x^2),x]
Main[Sin[x^2],x]
Main[e^x,x]
Main[Sqrt[a x+b],x]
Main[Sqrt[a x^2 +b x +c]+Sqrt[a x +b],x]
Main[Sqrt[x^2+1],x]
Main[a^x+a x,x]
Main[x^x,x]
Main[x a^x,x]*)



NotebookDirectory[]


IntTable[x^2,x]
NoClose[E^(x^2),x]
Main[x^2,x]
Main[(x+1)^2,x]
(*Main[(5x+2)/(3x+1),x]*)
intDDM[(x+1)^2,x]




