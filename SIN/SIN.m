(* ::Package:: *)

Main[f_,x_]:=Module[
	{e=f,right},
	SetDirectory[".\\"];
	Import["StageII.m"];
	Import["IntTable.m"];
	(*Import["NoCloseTable.m"];
	Import["intDDM.m"];*)
	
	(*Stage I Method I*)
	
	
	If[ Head[e]==Plus,
		If[ (Main[e[[1]],x]=!="NotFound")&&(Main[e[[2]],x]=!="NotFound"),
			Return[Main[e[[1]],x]+Main[e[[2]],x]]
		]
	];
	
	
	If[ Head[e]==Minus,
		If[ (Main[e[[1]],x]=!="NotFound")&&(Main[e[[2]],x]=!="NotFound"),
			Return[Main[e[[1]],x]-Main[e[[2]],x]]
		]
	];
	
	
	If[ Head[e]==Times,
		If[ (D[e[[1]],x]==0),
			Return[e[[1]]*Main[e[[2]],x]]
		];
		If[ (D[e[[2]],x]==0),
			Return[e[[2]]*Main[e[[1]],x]]
		];
	];
	
	
	(*Stage I Method II*)
	If[ Head[e]==Power,
		right=e[[2]];
		If[ (Head[right]==Integer&&right>0)&&(MatchQ[e,Plus]),
			Return[Main[Expand[e],x]]			
		];
	];
	
	(*If[ IntDDM[e,x]=!="NotMatch",
		Return[IntDDM[e,x]]
	];*)
	
	(*Check the table*)
	
	If[ IntTable[e,x]=!="NotFound",
		Return[IntTable[e,x]]
	];

	Return["NotFound"];
	If[ NoCloseTable[e,x]==="NoClose",
		Return["NoClose"]
	];

	(*Return[StageII[e,x]]*)
];


Main[1,x]


Main[5/(x^2),x]


Main[Sin[x^2],x]


Main[e^x,x]


Main[Sqrt[a x+b],x]


Main[Sqrt[a x^2 +b x +c]+Sqrt[a x +b],x]


Main[Sqrt[x^2+1],x]


Main[a^x+a x,x]


Main[x^x,x]


Main[x a^x,x]
