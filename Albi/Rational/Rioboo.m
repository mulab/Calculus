(* ::Package:: *)

(* Rioboo's conversion of complex logarithms to real arc-tangents *)
(* Reference: Bronstern05 P63 *)
LogToAtan::usage="Given a filed \[ScriptCapitalK] of characteristic 0 such that \!\(\*SqrtBox[\(-1\)]\)\[NotElement]\[ScriptCapitalK], and A,B\[Element]\[ScriptCapitalK][x] with B\[NotEqual]0, return a sum f of arctangents of polynomials in \[ScriptCapitalK][x] such that \!\(\*FractionBox[\(\[DifferentialD]f\), \(\[DifferentialD]x\)]\)=\!\(\*FractionBox[\(\[DifferentialD]\), \(\[DifferentialD]x\)]\)I*Log[\!\(\*FractionBox[\(A + I*B\), \(A - I*B\)]\)].";
LogToAtan[A_,B_,x_]:=Module[
	{q,r,D,C,G},
	{q,r}=PolyDivide[A,B,x];
	If[Simplify[r]==0,Return[2*ArcTan[q]]];
	If[Exponent[A,x]<Exponent[B,x],Return[LogToAtan[-B,A]]];
	{D,C,G}=ExtendedEuclidean[B,-A,x];
	2*ArcTan[First[PolyDivide[(A*D+B*C),G,x]]]+LogToAtan[D,C,x]
]


(* Rioboo's conversion of sums of complex logarithms to real functions *)
LogToReal[R_,S_,x_]:=Module[
	{},
	;
]


(* A=x^3-3x;
B=x^2-2;
f=LogToAtan[A,B,x]
Simplify[D[f,x]==D[I*Log[(A+I*B)/(A-I*B)],x]] *)
