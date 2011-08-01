(* ::Package:: *)

(* Method 8 in Stage II, (8)Rational functions *)
(* Last revised by ivan on 15:55 Aug 1, 2011. Email: ma_wan _li .6209@163.com *)
(* Now, it calls Horowitz-Ostrogradsky method to part the integrand into rational
	part and log part, then use Rothstein-Trager method to integrate the logpart*)
(* When the kernal realized function Apart and ApartSquareFree, this part
 should be reivsed (may be Hermite method?)*)
intSubRat[f_,x_]:=Module[
	{e=f,q,r,inte},	
	e=Simplify[e]; e=Together[e];
	r=Denominator[e];q=Numerator[e];
	If[!(PolynomialQ[r,x]&&PolynomialQ[q,x]),Return["NotMatch"];];
	If[(q/r)=!=e,Return["NotMatch"];];
	{Q1,r1,Q2,r2,x}=HorowitzOstrogradsky[q,r,x];
	Q2r2=Cancel[Q2/r2]; Q2=Numerator[Q2r2];r2=Denominator[Q2r2];
	inte=RothsteinTrager[Q2,r2,x];
(*Print["D=",D[inte,x]];	*)
	left = Simplify[f-Q1/r1-D[inte,x]];
	If[Left!=0,Print["LEFT = ",left];
		Print["If you see this, please report bug to ivan"]
	];
	If[inte==="CANNOT SOLVE",Return["NotMatch"],Return[Q1/r1+inte]]
]	
(*Problem remaining:
How to simplify expression like:
Log[f[x]-b I]-Log[f[x]+b I]====into=====2 I(ArcTan[f[x]/b]-Pi/2]
*)


intSubRat[x/(x^3+1),x]
intSubRat[1/(1+2x)/(1+x^2),x]
intSubRat[(x-2)/(x^2+2x+3),x]
intSubRat[(2x^3+2x^2+5x+5)/(x^4+5x^2+4),x]
intSubRat[1/(x^4+1),x]


mya=-(1/4) (-1)^(1/4) Log[(-1)^(1/4)-x]-1/4 (-1)^(3/4) Log[(-1)^(3/4)-x]+1/4 (-1)^(1/4) Log[(-1)^(1/4)+x]+1/4 (-1)^(3/4) Log[(-1)^(3/4)+x];
sta=ArcTan[(-1+x^2)/(Sqrt[2] x)]/(2 Sqrt[2])-Log[(1-Sqrt[2] x+x^2)/(1+Sqrt[2] x+x^2)]/(4 Sqrt[2]);
N[mya-sta/.x->10](*0.55536` -3.33067`*^-16 I left, do not change with x*)


(*Horowitz-Ostrogradsky method for rational function integration*)

HorowitzOstrogradsky[q_,r_,x_]:=Module[(*Input parameter is Numerator, Denominator, Variable*)
	{rAp,qAp,r1,r2,q1,q2,Q1,Q2},
	If[!(PolynomialQ[r,x]&&PolynomialQ[q,x]),Return["NotMatch"];];
	rAp=D[r,x];(*r'*)
	qAp=D[q,x];
	r1=PolynomialGCD[r,rAp];
	r2=r/r1;
	If[FreeQ[r1,x],Return[{0,1,q,r,x}];];

	Q1=Table[q1[i],{i,0,Exponent[r1,x]-1}]*Table[x^i,{i,0,Exponent[r1,x]-1}];
	Q2=Table[q2[i],{i,0,Exponent[r2,x]-1,1}]*Table[x^i,{i,0,Exponent[r2,x]-1}];
	Q1=Apply[Plus,Q1];Q2=Apply[Plus,Q2];(*generate polynominal q1,q2*)
	Q1Ap=D[Q1,x];
	ans=SolveAlways[Q1Ap r2 - Q1 (D[r1,x]/r1) r2 + Q2 r1 == q,x];
	(*Solve equation q=q1'r2-q1r1'r2/r1+q2r1*)
	Q1=Q1/.ans;Q2=Q2/.ans;(*Here we find the final expression of Q1 and Q2*)
	Q1=Cancel[Q1][[1]];Q2=Cancel[Q2[[1]]];r1=Cancel[r1];r2=Cancel[r2];
	Return[{Q1,r1,Q2,r2,x}](*q1/r1 is the rational part and q2/r2 is the log part*)
] 


(*HorowitzOstrogradsky[7(x)*(3x^2-2x),(x^6-4x^5+7)*(x-3)^3,x]*)
HorowitzOstrogradsky[x^7-24x^4-4x^2+8x-8,x^8+6x^6+12x^4+8x^2,x]


(* This function deserves more consideration *)
(* Pay attention to ArcTan*)


RothsteinTrager[q_,r_,x_]:=Module[(*Input parameter is Numerator, Denominator, Variable*)
	{res,roots,ci,vi,inte=0},

	res = Resultant[q-y D[r,x],r,x];
	roots = Roots[res==0,y]; (*get the roots ck or y and delete repeated ones*)
	If[roots==False,Return["CANNOT SOLVE"]];
	If[Head[roots]=!=Equal,roots = Union[roots];];   (*ATTENTION: Union often errors*)
	If[!FreeQ[roots,Root],Return["CANNOT SOLVE"],
		If[Head[roots]===Equal,len1=1,len1=Length[roots]](*len1 is the number of roots*)
	];
(*Print["roots=",roots];*)
	If[len1==1,
		ci = roots[[2]];
		vi = PolynomialGCD[q-ci D[r,x],r];
		Return[ci Log[vi]],
(*else*)For[ii=1,ii<=len1,ii++,
			ci=roots[[ii,2]];
			vi = PolynomialGCD[q-ci D[r,x],r,Extension->Automatic];
			inte = inte + ci Log[vi];
(*Print[q-ci D[r,x]];Print[r];Print["gcd=",vi];*)
		];
	];
	Return[inte];
]
RothsteinTrager[4x,x^2-4x+5,x]


(*Print["final ans=",RothsteinTrager[3x^2+1,x^3+x+1,x]];
Print["final ans=",RothsteinTrager[2x-3,(x-1)(x-2),x]];
Print[RothsteinTrager[x^4-3x^2+6,x^6-5x^4+5x^2+4,x]];

Print["final ans=",RothsteinTrager[x,x^3+2,x]];*)



RationalQ[(x^5+x^7+y^3)/(x^3+y^5),{x,y}]
