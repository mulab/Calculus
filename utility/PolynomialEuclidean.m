(* ::Package:: *)

Euclidean[A_,B_,x_]:=Module[
	{a=Simplify[A],b=Simplify[B],q,r},
	While[b=!=0,
		{q,r}=PolyDivide[a,b,x];
		a=b;
		b=Simplify[r];
	];
	a
]


(* Given a Euclidean domain D and a,b,c\[Element]D with c\[Element](a,b), return s,t,g\[Element]D such that g=gcd(a,b) and s*a+t*b=g *)
ExtendedEuclidean[A_,B_,x_]:=Module[
	{a=Simplify[A],b=Simplify[B],s,t,g,q,r,a1,b1,r1},
	a1=1;b1=0;
	While[b=!=0,
		{q,r}=PolyDivide[a,b,x];
		a=b;b=Simplify[r];
		r1=a1-q*b1;a1=b1;b1=r1;
	];
	{s,g}={a1,a};
	{t,r}=PolyDivide[g-s*A,B,x];
	{s,t,g}
]


ExtendedEuclidean[a_,b_,c_,x_]:=Module[
	{g,s,t,q,r},
	{s,t,g}=ExtendedEuclidean[a,b,x];
	q=First[PolyDivide[c,g,x]];
	(* deal with exception that r!=0 *)
	{s,t}=q*{s,t};
	{q,r}=PolyDivide[s,b,x];
	{r,Together[t+q*a]}
]


PartialFraction[A_,d_,x_]:=Module[
	{a0,a1,ai,b0,r,t},
	{a0,r}=PolyDivide[A,Times@@d,x];
	If[Length[d]==1,Return[{a0,r}]];
	{a1,t}=ExtendedEuclidean[Times@@d[[2;;]],d[[1]],r,x];
	{b0,ai}=PartialFraction[t,d[[2;;]],x];
	Flatten[{a0+b0,a1,ai}]
]


(* PartialFraction[x^2+3x,{x+1,x^2-2x+1},x]
ExtendedEuclidean[x^4-2x^3-6x^2+12x+15,x^3+x^2-4x-4,x]
Euclidean[x^4-2x^3-6x^2+12x+15,x^3+x^2-4x-4,x] *)
