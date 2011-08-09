(* ::Package:: *)

rischpoly[0,x_]:=0
rischpoly[a_:1,x_]:=a x/;FreeQ[a,x]
rischpoly[a_. x_^n_.,x_]:=(a x^(1+n))/(1+n)/;n=!=-1&&FreeQ[{a,n},x]
rischpoly[a_+b_,x_]:=rischpoly[a,x]+rischpoly[b,x]
rischpoly[a_./x_,x_]:=a Log[x]/;FreeQ[a,x]


(*Reference: Symbolic Integration 1, Manuel Bronstein, Springer, 2005.*)
HermiteReduce[a_,d_,var_]:=Module[
	{num=a,den=d,g=0, polyPart=0,Sn,Ss,Sn2,Sns,B,c},
	If[Exponent[a,var]>=Exponent[d,var],
		polyPart=rischpoly[PolynomialQuotient[a,d,var],var]; 
		num=PolynomialRemainder[a,d,var];
	];
	Sn=PolynomialGCD[den,D[den,var]];
	Ss=Cancel[den/Sn];
	While[Exponent[Sn,var]>0,
		Sn2=PolynomialGCD[Sn,D[Sn,var]];
		Sns=Cancel[Sn/Sn2];
		{B,c}=PolynomialExtendedGCD[-Cancel[(Ss D[Sn,var])/Sn],Sns,num,var];
		num=c-Cancel[(D[B,var] Ss)/Sns];
		g=g+B/Sn;
		Sn=Sn2;
	];
	{polyPart+Cancel[g],Cancel[num/Ss]}
]
