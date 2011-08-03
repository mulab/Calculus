(* ::Package:: *)

(*the integral is of the form R (x,Sqrt[c*x^2+b*x+a]),
where a,b,c are constants (c!=0&a^2+b^2!=0) and R is a rational function of its arguments*)
(*the method 5 of SIN ( Symbolic INtegrator ) stage II*)
(*Shao Qiming & Zhang Junlin*)
intSubSqt[f_,x_]:=Module[
	{e=f,pos,loci,et,y,sqt,a=Null,b=Null,c=Null,A,C,a1,c1},
	pos=Position[e,Power[Plus[_,__],Rational[_Integer,2]]];
	If[pos==={},Return["NotMatch"]];(*do not have Sqrt[c*x^2+b*x+a]*)	
	If[!PolynomialQ[et,x],Return["NotMatch"]];
	Do[
		loci=pos[[1]];
		et=Extract[e,loci];
		sqt=et[[1]];
		If[PolynomialQ[sqt,x],(*then*)
		b=Coefficient[sqt,x];
		c=Coefficient[sqt,x^2];
		a=sqt-b x -c x^2;
		Break[],(*else*)
		Continue[]
		],
		{i,Length[pos]}
	];
	If[a===Null,Return["NotMatch"]];
	A=a-b^2/(4 c);
	C=c;
	e=e/.x->(y-b/(2 c));
	a1=defin1[A];c1=defin1[C];
	If[c1>0 && a1>0,
		e=e/.y->(Tan[z]*Sqrt[A/C]);
		e=e*D[Tan[z]*Sqrt[A/C],z];(*\:5229\:7528\:5fae\:5206\:6765\:5904\:7406\:6362\:5143*)
		Assuming[e>0&&e<Pi/2,e=Simplify[e]];(*\:5047\:8bbez\:4f4d\:4e8e\:7b2c\:4e00\:8c61\:9650\:ff0c\:8fdb\:884c\:5904\:7406*)
		Return[{e,z,ArcTan[Sqrt[C/A]*(x+b/(2 c))]}]
	];
	If[c1>0 && a1<0,(*\:8be5\:60c5\:51b5\:548c\:7b2c\:56db\:79cd\:60c5\:51b5\:8c8c\:4f3cMoses\:7684\:4e66\:4e0a\:5199\:9519\:4e86*)
		e=e/.y->(Sec[z]*Sqrt[-A/C]);
		e=e*D[Sec[z]*Sqrt[-A/C],z];
		Assuming[e>0&&e<Pi/2,e=Simplify[e]];
		Return[{e,z,ArcSec[Sqrt[C/-A]*(x+b/(2 c))]}]
	];
	If[c1>0 && a1==0,
		e=e/.y->(z/Sqrt[C]);
		e=e/Sqrt[C];
		Assuming[e>0&&e<Pi/2,e=Simplify[e]];
		Return[{e,z,Sqrt[C]*(x+b/(2 c))}]
	];
	If[c1<0 && a1>0,
		e=e/.y->(Sin[z]*Sqrt[-A/C]);
		e=e*Sqrt[-A/C]*Cos[z];
		Assuming[e>0&&e<Pi/2,e=Simplify[e]];
		Return[{e,z,ArcSin[Sqrt[C/-A]*(x+b/(2 c))]}]
	];
	Print[{A,C}];	
	Return["NotMatch"]
]



(*\:5982\:679c\:7cfb\:6570\:4e3a\:53c2\:6570\:ff0c\:9ed8\:8ba4\:4e3a1\:ff0c\:8fdb\:884c\:5224\:65ad*)
defin1[f_]:=Module[
{e=f,temp,i,pos},
pos=Position[e,_Symbol];
(*Print[Extract[e,pos]];*)
If[Length[pos]==0,Return[e]];
	Do[
		temp=Extract[e,pos[[i]]];
		If[temp=!=Plus&&temp=!=Times&&temp=!=Power,(*then*)
		e=ReplacePart[e,pos[[i]]->1]
		],
		{i,Length[pos]}
	];
Return[e];
]


(*intSubSqt[x^4/(1-x^2)^(5/2),x]
intSubSqt[x/(1-5x+x^2)^(5/2),x]
intSubSqt[(3x+2)/Sqrt[4x^2+2]+Sqrt[4x^2+2],x]
intSubSqt[(3x+2)/Sqrt[5x^2+x+3]+Sqrt[4x^2+2],x]
intSubSqt[Sqrt[A^2+B^2-B^2 x^2]/(1-x^2),x]*)







