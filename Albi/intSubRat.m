(* ::Package:: *)

(* Method 8 in Stage II, (8)Rational functions *)
(* Last revised by ivan on 17:50 Aug 4, 2011. Email: ma_wan _li .6209@163.com *)
(* Now, it calls Horowitz-Ostrogradsky method to part the integrand into rational
	part and log part, then use Rothstein-Trager method to integrate the logpart,
	and then use Log2Arctan to transform the result into usual format. *)
(* When the kernal realized function Apart and ApartSquareFree, this part
 might be improved (may be Hermite method?)*)
(* Problem remaining: 
	a) Temporarily cannot handle such form as (-1)^(1/4);
	b)	*)


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


(*HorowitzOstrogradsky[7(x)*(3x^2-2x),(x^6-4x^5+7)*(x-3)^3,x]
HorowitzOstrogradsky[x^7-24x^4-4x^2+8x-8,x^8+6x^6+12x^4+8x^2,x]*)


RothsteinTrager[q_,r_,x_]:=Module[(*Input parameter is Numerator, Denominator, Variable*)
	{len1,res,roots,ci,vi,y,inte=0},
	If[FreeQ[r,x],Return[0]];
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


(*RothsteinTrager[4x,x^2-4x+5,x]
RothsteinTrager[x,x+1,x]
RothsteinTrager[3x+5,x^5-1,x]
RothsteinTrager[4x,x^2-4x+5,x]*)


(*Print["final ans=",RothsteinTrager[3x^2+1,x^3+x+1,x]];
Print["final ans=",RothsteinTrager[2x-3,(x-1)(x-2),x]];
Print[RothsteinTrager[x^4-3x^2+6,x^6-5x^4+5x^2+4,x]];

Print["final ans=",RothsteinTrager[x,x^3+2,x]];*)



(* See page 75 of Symbolic integration by Bronstein*)
(* This part change the output of RothsteinTrager from Log form to ArcTan form:
	I Log[(A + B I)/(A - B I)] --> 2ArcTan(A/B)   *)
(* This part need package .\\Rational \\ Rioboo.m*)
Log2ArcTan[f_,x_]:=Module[
	{e=f,pos,re,im,vi,jj,kk,viconj,ci,ciconj,A,B,ifvieqreal,todelete,ans},
	If[Head[f]=!=Plus,Print["Log2ArcTan NotMatch"];Return[f];];
	pos = Position[f,Log[_]]; (* Log[vi_] *)
	pos = Map[Append[#,1]&,pos];(* vi_ *)

	vi=Extract[f,pos];
	ci = Level[f,1]/Log[vi];

	ifvieqreal = Map[FreeQ[Extract[f,#],Complex]&,pos];
	todelete = Position[ifvieqreal,True];
	(*
	 Another to find the todelete matrix
	todelete={};(*This part delete ci Log[vi] in which vi=Real *)
	For[i=1,i<=Length[pos],i++,
		If[FreeQ[Extract[f,pos[[i]]],Complex],
			AppendTo[todelete,{i}];
		];
	];
    *)

	pos= Delete[pos,todelete];
	vi = Delete[vi,todelete];
	ci = Delete[ci,todelete];
(*Print["vi = ",vi];
Print["ci = ",ci];*)
	(*viconj = vi/.(Complex[re_,im_]->Complex[re,-im]);*)
	ciconj = ci/.(Complex[re_,im_]->Complex[re,-im]);

	ans = 0;
	For[jj=1,jj<=Length[vi],jj++,
		For[kk=1,kk<=Length[vi],kk++,
			If[ci[[jj]]==ciconj[[kk]],

				A = (vi[[jj]]+vi[[kk]])/2;
				B = (vi[[jj]]-vi[[kk]])/2/I;
				Arctanpart = Calculus`Albi`Rational`LogToAtan[A,B,x];
				Cp = Simplify[ci[[jj]]+ciconj[[jj]]];
				Cn = Simplify[ci[[jj]]-ciconj[[jj]]];
				Logpart = Simplify[A^2+B^2];
				
(*Print["A=",A];
Print["B=",B];
Print["A+B I=",Simplify[A+B I]];
Print["A-B I=",Simplify[A-B I]];
Print["Logpart",Logpart];
Print["Arctanpart",Arctanpart];
Print["c+=",Cp];
Print["c-=",Cn];*)
				ans = ans + Cp/4 Log[Logpart] + Cn/4/I Arctanpart;
				e = e-ci[[jj]] Log[vi[[jj]]];
			];
		];
	];
(*Print["left = ",e];			
Print["new  = ",ans];*)
	Return[ans+e];
]
(*
Clear [x];
Log2ArcTan[(-(1/5)+I/10) Log[(-(2/5)+I/5)+(1/5+(2 I)/5) x]+2/5 Log[1/5+(2 x)/5]-(1/5+I/10) Log[(1/5-(2 I)/5)+(2/5+I/5) x],x]
SequenceForm["Standard Answer = ", Rational[1, 5] ArcTan[x] + Rational[2, 5] Log[1 + 2 x] + Rational[-1, 5] Log[1 + x^2]]*)


(*
(*BUG!*)
(* See page 75 of Symbolic integration by Bronstein*)
(* This part change the output of RothsteinTrager from Log form to ArcTan form:
	I Log[(A + B I)/(A - B I)] --> 2ArcTan(A/B)   *)
(* This part need package .\\Rational \\ Rioboo.m*)
Log2ArcTan[f_,x_]:=Module[
	{pos,re,im,vi,viconj,vireal,viimag,ci,ciconj,cireal,ciimag,ifvieqreal,todelete,ans,dealed},
	If[Head[f]=!=Plus,Print["Log2ArcTan NotMatch"];Return[f];];
	pos = Position[f,Log[_]]; (* Log[vi_] *)
	pos = Map[Append[#,1]&,pos];(* vi_ *)
Print["f=",f];
	vi=Extract[f,pos];
	ci = Level[f,1]/Log[vi];

	ifvieqreal = Map[FreeQ[Extract[f,#],Complex]&,pos];
	todelete = Position[ifvieqreal,True];
	(*
	 Another to find the todelete matrix
	todelete={};(*This part delete ci Log[vi] in which vi=Real *)
	For[i=1,i<=Length[pos],i++,
		If[FreeQ[Extract[f,pos[[i]]],Complex],
			AppendTo[todelete,{i}];
		];
	];
    *)

	pos= Delete[pos,todelete];
	vi = Delete[vi,todelete];
	ci = Delete[ci,todelete];

	viconj = vi/.(Complex[re_,im_]->Complex[re,-im]);
	vireal = Simplify[(vi+viconj)/2];
	viimag = Simplify[(vi-viconj)/2/I];

	ciconj = ci/.(Complex[re_,im_]->Complex[re,-im]);
	cireal = Simplify[(ci+ciconj)/2];
	ciimag = Simplify[(ci-ciconj)/2/I];

	ans = cireal/2 Log[vireal^2+viimag^2]+ ciimag ArcTan[vireal/ viimag];
	ans[[0]]=Plus; 
	dealed = ci Log[vi];  (* this part from f has been transformed into ArcTan form*)
	dealed[[0]]=Plus;
Print[dealed];
	Return[ans+f-dealed];
			(* generate answer with ArcTan form*)
]*)


(*f=(-(1/5)+I/10) Log[(-(2/5)+I/5)+(1/5+(2 I)/5) x]+2/5 Log[1/5+(2 x)/5]-(1/5+I/10) Log[(1/5-(2 I)/5)+(2/5+I/5) x];
f=-(1/3) (-1)^(2/3) Log[(-1)^(1/3)-x]-1/3 Log[1+x]+1/3 (-1)^(1/3) Log[-1+(-1)^(1/3)+x];
f=1/4 (2-3 I Sqrt[2]) Log[-I+Sqrt[2]-I x]+1/4 (2+3 I Sqrt[2]) Log[I+Sqrt[2]+I x]
ans=Log2ArcTan[f,x]
N[(ans-f)/.x->1]*)
(*ClearAll[Evaluate[Context[] <> "*"]]*)



(* Method 8 in Stage II, (8)Rational functions *)
intSubRat[f_,x_]:=Module[
	{e=f,q,r,inte,inteatan},	
	e=Simplify[e]; e=Together[e];
	r=Denominator[e];q=Numerator[e];
	If[!(PolynomialQ[r,x]&&PolynomialQ[q,x]),Return["NotMatch"];];
	If[Exponent[q,x]>=Exponent[r,x],Return["NotMatch"];];
	If[(q/r)=!=e,Return["NotMatch"];];
	{Q1,r1,Q2,r2,x}=HorowitzOstrogradsky[q,r,x];
	Q2r2=Cancel[Q2/r2]; Q2=Numerator[Q2r2];r2=Denominator[Q2r2];
	inte=RothsteinTrager[Q2,r2,x];
(*Print["D=",D[inte,x]];	*)
	left = Simplify[f-Q1/r1-D[inte,x]];
	inteatan  = Log2ArcTan[inte,x];
	If[inte_atan=!="NotMatch",inte = inteatan];
	If[Left!=0,Print["LEFT = ",left];
		Print["If you see this, please report bug to ivan"]
	];
	If[inte==="CANNOT SOLVE",Return["NotMatch"],Return[Q1/r1+inte]]
]	
(*Problem remaining:
How to simplify expression like:
1 Log[f[x]-b I]-Log[f[x]+b I]====into=====2 I(ArcTan[f[x]/b]-Pi/2]? See Bronstein's book
2 in RothsteinTrager, the PolynomialGCD sometimes returns expr. with "Root". Why does
	PolynomialGCD need Root?-
*)



(*intSubRat[x/(x^3+1),x]
intSubRat[1/(1+2x)/(1+x^2),x]
intSubRat[(x-2)/(x^2+2x+3),x]
intSubRat[(2x^3+2x^2+5x+5)/(x^4+5x^2+4),x]
intSubRat[1/(x^4+1),x]
intSubRat[1/(1+2 x+x^2),x]*)
(*
(* test script*)
f=x/(x^3+1)
std = Integrate[f,x];
Print["Standard Answer = ",std];
ans = intSubRat[f,x];
Print["ans = ",ans];
Print["N=",Abs[N[(D[ans,x]-f)/.x->3]]];
Print["error to std=", FullSimplify[std-ans]];*)




