(* ::Package:: *)

BeginPackage["Calculus`"]
D`usage="";
CWD::usage="Current Work Directory";
IntegrateU::usage="IntegrateU[f[x],x] returns the integral";


(* Special Functions *)
Unprotect[SinIntegral, CosIntegral, SinhIntegral, CoshIntegral, FresnelC, FresnelS];
SinIntegral::usage = "SinIntegral[x] gives the sine integral
Integrate[Sin[t]/t, {t, 0, x}].";
CosIntegral::usage = "CosIntegral[x] gives the cosine integral
EulerGamma + Log[x] + Integrate[(Cos[t] - 1)/t, {t, 0, x}].";
SinhIntegral::usage = "SinhIntegral[x] gives the hyperbolic sine integral
Integrate[Sinh[t]/t, {t, 0, x}].";
CoshIntegral::usage = "CoshIntegral[x] gives the hyperbolic cosine integral
EulerGamma + Log[x] + Integrate[(Cosh[t] - 1)/t, {t, 0, x}].";
FresnelS::usage = "FresnelS[x] gives the Fresnel integral
S[x] = Integrate[Sin[Pi t^2/2], {t, 0, x}].";
FresnelC::usage = "FresnelC[x] gives the Fresnel integral
C[x] = Integrate[Cos[Pi t^2/2], {t, 0, x}].";



Get[CWD<>"\\IntegralFunctions.m"];
(*Get[CWD<>"\\utility\\init.m"];*)
Get[CWD<>"\\Rubi\\init.m"];
Get[CWD<>"\\Albi\\init.m"];
(* Get[NotebookDirectory[]<>"D.u"]; *)
Get[CWD<>"Integrate.m"];
End[];


(* Special Functions *)
Attributes[SinIntegral] = {Listable, NumericFunction, ReadProtected};
Attributes[CosIntegral] = {Listable, NumericFunction, ReadProtected};
Attributes[SinhIntegral] = {Listable, NumericFunction, ReadProtected};
Attributes[CoshIntegral] = {Listable, NumericFunction, ReadProtected};
Attributes[FresnelS] = {Listable, NumericFunction, ReadProtected};
Attributes[FresnelC] = {Listable, NumericFunction, ReadProtected};

Protect[SinIntegral, CosIntegral, SinhIntegral, CoshIntegral, FresnelS, FresnelC];


Remove[CWD];
EndPackage[];


(*IntegrateU[x,x]
IntegrateU[Sqrt[1+(2 x)/(1+x^2)],x]*)



