(* ::Package:: *)

(*the integral is of the form R (x,Sqrt[c*x^2+b*x+a]),where a,b,c are constants (c!=0&a^2+b^2!=0) and R is a rational function of its arguments*)
intSubSqt[f_,x_]:=Catch[
	Module[
	{e=f,pos,loci,et,y,sqt,a=Null,b=Null,c=Null,A,C},
	pos=Position[e,Power[Plus[_,__],Rational[_Integer,2]]];
	If[pos==={},Throw["NotMatch"]];(*do not have Sqrt[c*x^2+b*x+a]*)
	et=ReplacePart[e,pos->y];
	If[!RationalQ[et,{x,y}],Throw["NotMatch"]];(*is not a rational form*)
	Do[
		loci=pos[[i]];
		sqt=Extract[e,Append[loci,1]];(*sqt=cx^2+bx+a*)
		If[FreeQ[sqt,x],Continue[]];(*sqt is irrelevant to x*)
		If[a=!=Null,
			If[MatchQ[sqt,a+b*x+c*x^2],
				Continue[],
				Throw["NotMatch"]
			]
		];
		If[MatchQ[sqt,a_.+b_.*x+c_.*x^2/;FreeQ[{a,b,c},x]],(*form a+bx+cx^2 or bx+cx^2*)
			a=Extract[sqt,{1}];
			If[FreeQ[a,x],(*form a+bx+cx^2*)
				b=Extract[sqt,{2}]/x;
				c=Extract[sqt,{3}]/x^2,
				b=a/x;(*form bx+cx^2*)
				a=0;
				c=Extract[sqt,{2}]/x^2
			],
			If[MatchQ[sqt,a_.+c_.*x^2/;FreeQ[{a,c},x]],(*form a+cx^2*)
				a=Extract[sqt,{1}];
				b=0;
				c=Extract[sqt,{2}]/x^2,
				Throw["NotMatch"]
			]
		],
		{i,Length[pos]}
	];
	A=a-b^2/(2c);
	C=c;
	e=e/.x->(y-b/(2c));
	If[C>0 && A>0,
		e=e/.y->(Tan[z]/Sqrt[C/A]);
		Throw[{Simplify[e],z,ArcTan[Sqrt[C/A]*(x+b/(2c))]}]
	];
	If[C>0 && A<0,
		e=e/.y->(Sec[z]/Sqrt[C/-A]);
		Throw[{Simplify[e],z,ArcSec[Sqrt[C/-A]*(x+b/(2c))]}]
	];
	If[C>0 && A==0,
		e=e/.y->(z/Sqrt[C]);
		Throw[{Simplify[e],z,Sqrt[C]*(x+b/(2c))}]
	];
	If[C<0 && A>0,
		e=e/.y->(Sin[z]*Sqrt[C/-A]);
		Throw[{Simplify[e],z,ArcSin[Sqrt[C/-A]*(x+b/(2c))]}]
	];
	Throw["NotMatch"]
	]
]


(*
intSubSqt[x^4/(1-x^2)^(5/2),x]
intSubSqt[x/(1-5x+x^2)^(5/2),x]
intSubSqt[(3x+2)/Sqrt[4x^2+2]+Sqrt[4x^2+2],x]
intSubSqt[(3x+2)/Sqrt[5x^2+x+3]+Sqrt[4x^2+2],x]
*)



