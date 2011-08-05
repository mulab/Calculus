(* ::Package:: *)

BeginPackage["Calculus`Utility`"];
RationalQ::usage="RationalQ[f,L]\:5224\:65ad\:51fd\:6570\:662f\:5426\:4e3a\:6709\:7406\:5206\:5f0f\:ff0c\:4e0d\:5904\:7406\:5e26\:53c2\:6570\:7684\:6709\:7406\:5f0f\:4ee5\:53ca\:4e24\:9879\:76f8\:52a0\:7684\:6709\:7406\:5f0f";
PolyDivide::usage="\:4e00\:5143\:591a\:9879\:5f0f\:9664\:6cd5";
ExtendedEuclidean::usage="Given a Euclidean domain \[CapitalDifferentialD] and a,b,c\[Element]\[CapitalDifferentialD], return s,t\[Element]\[CapitalDifferentialD] such that s*a+t*b=c and either s==0 or deg(s)<deg(b)";
PartialFraction::usage="Given a Euclidean domain \[CapitalDifferentialD], a positive integer n and a,\!\(\*SubscriptBox[\(d\), \(1\)]\),...,\!\(\*SubscriptBox[\(d\), \(n\)]\)\[Element]\[CapitalDifferentialD]\{0} with GCD[\!\(\*SubscriptBox[\(d\), \(i\)]\),\!\(\*SubscriptBox[\(d\), \(j\)]\)]==1 for i\[NotEqual]j, return \!\(\*SubscriptBox[\(a\), \(1\)]\),...,\!\(\*SubscriptBox[\(a\), \(n\)]\)\[Element]\[CapitalDifferentialD] such that \!\(\*FractionBox[\(a\), \(\(\*SubscriptBox[\(d\), \(1\)] ... \) \*SubscriptBox[\(d\), \(n\)]\)]\)=\!\(\*SubscriptBox[\(a\), \(0\)]\)+\!\(\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(n\)]\)\!\(\*FractionBox[SubscriptBox[\(a\), \(i\)], SubscriptBox[\(d\), \(i\)]]\) and either \!\(\*SubscriptBox[\(a\), \(i\)]\)==0 or deg(\!\(\*SubscriptBox[\(a\), \(i\)]\))<deg(\!\(\*SubscriptBox[\(d\), \(i\)]\)) for i\[GreaterEqual]1";


Begin["`Private`"];
If[Head[Calculus`CWD]===String,
	UtilityDIR=Calculus`CWD<>"Rubi\\original\\",
	UtilityDIR=NotebookDirectory[]<>"original\\"
];
Get[UtilityDIR<>"RationalQ.m"];
Get[UtilityDIR<>"PolyDivide.m"];
Get[UtilityDIR<>"PolynomialEuclidean.m"];
(*Get[NotebookDirectory[]<>"Simplify.u"];*)
End[];


EndPackage[];
