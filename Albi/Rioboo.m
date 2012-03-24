(* ::Package:: *)

(* Rioboo's conversion of complex logarithms to real arc-tangents *)
(* Reference: Bronstern05 P63 *)
LogToAtan::usage="Given a filed \[ScriptCapitalK] of characteristic 0 such that \!\(\*SqrtBox[\(-1\)]\)\[NotElement]\[ScriptCapitalK], and A,B\[Element]\[ScriptCapitalK][x] with B\[NotEqual]0, return a sum f of arctangents of polynomials in \[ScriptCapitalK][x] such that \!\(\*FractionBox[\(\[DifferentialD]f\), \(\[DifferentialD]x\)]\)=\!\(\*FractionBox[\(\[DifferentialD]\), \(\[DifferentialD]x\)]\)I*Log[\!\(\*FractionBox[\(A + I*B\), \(A - I*B\)]\)].";
LogToAtan[A_,B_,x_]:=Module[
	{q,r,D,C,G},
	(*{q,r}=Calculus`Utility`PolyDivide[A,B,x];*)
	q = PolynomialQuotient[A,B,x];
	r = PolynomialRemainder [A,B,x];
	If[Simplify[r]==0,Return[2*ArcTan[q]]];
	If[Exponent[A,x]<Exponent[B,x],Return[LogToAtan[-B,A,x]]];
	(*{D,C,G}=Calculus`Utility`ExtendedEuclidean[B,-A,x];*)
	{G,{D,C}}=PolynomialExtendedGCD[B,-A,x];
	(*2*ArcTan[First[Calculus`Utility`PolyDivide[(A*D+B*C),G,x]]]+LogToAtan[D,C,x]*)
	2*ArcTan[PolynomialQuotient[(A*D+B*C),G,x]]+LogToAtan[D,C,x]
]


(* Rioboo's conversion of sums of complex logarithms to real functions *)
(* Reference: Bronstern05 P69 *)
(* !!NOT Finished yet!! *)
LogToReal::usage="Given a real field \[ScriptCapitalK], R\[Element]\[ScriptCapitalK][t] and S\[Element]\[ScriptCapitalK][t,x], return a real function f such that \!\(\*FractionBox[\(\[DifferentialD]f\), \(\[DifferentialD]x\)]\)=\!\(\*FractionBox[\(\[DifferentialD]\), \(\[DifferentialD]x\)]\)\!\(\*UnderscriptBox[\(\[Sum]\), \(\[Alpha] | R[\[Alpha]] = 0\)]\)\[Alpha]*Log[S[\[Alpha],x]].";
LogToReal[R_,S_,t_,x_]:=Module[
	{P,Q,A,B,tmp,u,v,ans},
	tmp=R/.x->u+I*v;
	P=Re[tmp];
	Q=Im[tmp];
	tmp=S/.t->u+I*v;
	A=Re[tmp];
	B=Im[tmp];
	tmp=SolveAlways[v>0&&P==0&&Q==0,{u,v}];
	ans
]


(*A=x^3-3x;
B=x^2-2;
A=1/2 (-2 (1+1/4 (2-3 I Sqrt[2]))-2 (1+1/4 (2+3 I Sqrt[2]))+(1+1/2 (-2-3 I Sqrt[2])) x+(1+1/2 (-2+3 I Sqrt[2])) x);
B=-(1/2) I (2 (1+1/4 (2-3 I Sqrt[2]))-2 (1+1/4 (2+3 I Sqrt[2]))+(1+1/2 (-2-3 I Sqrt[2])) x-(1+1/2 (-2+3 I Sqrt[2])) x);
f=LogToAtan[A,B,x]
Simplify[D[f,x]==D[I*Log[(A+I*B)/(A-I*B)],x]] *)


(* this function is part of utilities of Albi*)
(* See page 75 of Symbolic integration by Bronstein*)
(* This part change the output of RothsteinTrager from Log form to ArcTan form:
	I Log[(A + B I)/(A - B I)] --> 2ArcTan(A/B)   *)
Log2ArcTan[f_,x_]:=Module[
	{e},
	e = f//.ci1_ Log[vi1_]+ci2_ Log[vi2_]/;FreeQ[Simplify[ci1+ci2],Complex]->(Simplify[ci1+ci2])/2 Log[Simplify[((vi1+vi2)/2)^2+((vi1-vi2)/2/I)^2]] + Simplify[ci1-ci2]/2/I LogToAtan[((vi1+vi2)/2),((vi1-vi2)/2/I),x];
	e = FullSimplify[e];
	Return[e];
]
