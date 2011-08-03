(* ::Package:: *)

BeginPackage["Rubi`"];

Int::usage="Int[f[x],x] returns the integral";

Begin["`Private`"];

SetDirectory[NotebookDirectory[]];

Get["TableInt.m"];
Get["NoCloseInt.m"];

Get["original\\RationalFunctions\\RationalFunctionsNew.m"]
Get["original\\RationalFunctions\\RationalFunctionsOfLinears.m"];
Get["original\\RationalFunctions\\RationalFunctionsOfBinomials.m"];
Get["original\\RationalFunctions\\RationalFunctionsOfTrinomials.m"];

Get["original\\AlgebraicFunctions\\AlgebraicFunctionsNew.m"];
Get["original\\AlgebraicFunctions\\AlgebraicFunctionsOfLinears.m"];
Get["original\\AlgebraicFunctions\\AlgebraicFunctionsOfBinomials.m"];
Get["original\\AlgebraicFunctions\\AlgebraicFunctionsOfTrinomials.m"];

Get["original\\ExponentialFunctions\\ExponentialFunctions.m"];
Get["original\\ExponentialFunctions\\ProductsOfExponentialAndTrigFunctions.m"];
Get["original\\ExponentialFunctions\\ProductsOfExponentialAndHyperbolicFunctions.m"];
Get["original\\ExponentialFunctions\\LogarithmFunctionsNew.m"];
Get["original\\ExponentialFunctions\\LogarithmFunctions.m"];

Get["original\\TrigFunctions\\TrigFunctionsNew.m"];
Get["original\\TrigFunctions\\SineFunctions.m"];
Get["original\\TrigFunctions\\TangentFunctions.m"];
Get["original\\TrigFunctions\\SecantFunctions.m"];
Get["original\\TrigFunctions\\(sin^j)^m (a+a sin^k)^n.m"];
Get["original\\TrigFunctions\\(sin^j)^m (a+b sin^k)^n.m"];
Get["original\\TrigFunctions\\(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
Get["original\\TrigFunctions\\(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
Get["original\\TrigFunctions\\(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
Get["original\\TrigFunctions\\(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
(*Get["original\\TrigFunctions\\DomainMapOfIntegrationRules.m"];*)
Get["original\\TrigFunctions\\RationalFunctionsOfSinesAndCosines.m"];
Get["original\\TrigFunctions\\TwoTrigFunctions.m"];
Get["original\\TrigFunctions\\TrigNormalization.m"];
Get["original\\TrigFunctions\\TrigSubstitution.m"];

Get["original\\InverseTrigFunctions\\InverseTrigFunctionsNew.m"];
Get["original\\InverseTrigFunctions\\InverseSineFunctions.m"]; 
Get["original\\InverseTrigFunctions\\InverseCosineFunctions.m"];
Get["original\\InverseTrigFunctions\\InverseTangentFunctions.m"];
Get["original\\InverseTrigFunctions\\InverseCotangentFunctions.m"];
Get["original\\InverseTrigFunctions\\InverseSecantFunctions.m"];
Get["original\\InverseTrigFunctions\\InverseCosecantFunctions.m"];

Get["original\\HyperbolicFunctions\\HyperbolicSineFunctions.m"];
Get["original\\HyperbolicFunctions\\HyperbolicTangentFunctions.m"];
Get["original\\HyperbolicFunctions\\HyperbolicSecantFunctions.m"];
Get["original\\HyperbolicFunctions\\RationalFunctionsOfHyperbolicSinesAndCosines.m"];
Get["original\\HyperbolicFunctions\\TwoHyperbolicFunctions.m"];
Get["original\\HyperbolicFunctions\\HyperbolicSubstitution.m"];
Get["original\\HyperbolicFunctions\\RationalFunctionsOfHyperbolicSines.m"];

Get["original\\InverseHyperbolicFunctions\\InverseHyperbolicSineFunctions.m"];
Get["original\\InverseHyperbolicFunctions\\InverseHyperbolicCosineFunctions.m"];
Get["original\\InverseHyperbolicFunctions\\InverseHyperbolicTangentFunctions.m"];
Get["original\\InverseHyperbolicFunctions\\InverseHyperbolicCotangentFunctions.m"];
Get["original\\InverseHyperbolicFunctions\\InverseHyperbolicSecantFunctions.m"];
Get["original\\InverseHyperbolicFunctions\\InverseHyperbolicCosecantFunctions.m"];

Get["original\\SpecialFunctions\\ErrorFunctions.m"];
Get["original\\SpecialFunctions\\FresnelIntegralFunctions.m"];
Get["original\\SpecialFunctions\\ExponentialIntegralFunctions.m"];
Get["original\\SpecialFunctions\\TrigIntegralFunctions.m"];
Get["original\\SpecialFunctions\\HyperbolicIntegralFunctions.m"];
Get["original\\SpecialFunctions\\LogarithmIntegralFunctions.m"];
Get["original\\SpecialFunctions\\GammaFunctions.m"];
Get["original\\SpecialFunctions\\ZetaFunctions.m"];
Get["original\\SpecialFunctions\\PolylogarithmFunctions.m"];
Get["original\\SpecialFunctions\\ProductLogarithmFunctions.m"];

Get["original\\GeneralIntegrationRules.m"];
Get["original\\IntegrationUtilityFunctions.m"]; 

End[];
EndPackage[];


(*Int[E^x,x]
Int[x^4*(1-x^2)^(-5/2),x]
Int[x^(1/2)*(1+x)^(5/2),x]
Int[Log[3*(4*(5+6*x)^7)^2],x]
Int[(x^3)^(-1/3),x]
Int[x E^x]*)

(*Int[(a+b*Sqrt[x])^20/Sqrt[x],x]*)
(*Int[(1-2 Sqrt[x])^20/Sqrt[x],x]*)
