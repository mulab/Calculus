(* ::Package:: *)

(* ::Code:: *)
Int[LogIntegral[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@LogarithmIntegralFunctions.m"];
  (a+b*x)*LogIntegral[a+b*x]/b - ExpIntegralEi[2*Log[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*LogIntegral[a_.+b_.*x_],x_Symbol] :=
(Print["Int(2th)@LogarithmIntegralFunctions.m"];
  x^(m+1)*LogIntegral[a+b*x]/(m+1) -
  Dist[b/(m+1),Int[x^(m+1)/Log[a+b*x],x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]
