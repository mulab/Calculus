(* ::Package:: *)

ExtendedEuclidean[a_,b_,c_,x_]:=Module[
	{g,s,t,q,r},
	{g,{s,t}}=PolynomialExtendedGCD[a,b,x];
	q=First[PolynomialQuotientRemainder[c,g,x]];
	(* deal with exception that r!=0 *)
	{s,t}=q*{s,t};
	{q,r}=PolynomialQuotientRemainder[s,b,x];
	{r,Together[t+q*a]}
]


PartialFraction[A_,d_,x_]:=Module[
	{a0,a1,ai,b0,r,t},
	{a0,r}=PolynomialQuotientRemainder[A,Times@@d,x];
	If[Length[d]==1,Return[{a0,r}]];
	{a1,t}=ExtendedEuclidean[Times@@d[[2;;]],d[[1]],r,x];
	{b0,ai}=PartialFraction[t,d[[2;;]],x];
	Flatten[{a0+b0,a1,ai}]
]


(* PartialFraction[x^2+3x,{x+1,x^2-2x+1},x] *)
