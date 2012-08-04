(* ::Package:: *)

(* ::Code:: *)
Int[SinIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*SinIntegral[a+b*x]/b + Cos[a+b*x]/b/;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[CosIntegral[a_.+b_.*x_],x_Symbol] :=
(Print["Int(2th)@TrigIntegralFunctions.m"];
  (a+b*x)*CosIntegral[a+b*x]/b - Sin[a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[SinIntegral[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(3th)@TrigIntegralFunctions.m"];
  (a+b*x)*SinIntegral[a+b*x]^2/b -
  Dist[2,Int[Sin[a+b*x]*SinIntegral[a+b*x],x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[CosIntegral[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(4th)@TrigIntegralFunctions.m"];
  (a+b*x)*CosIntegral[a+b*x]^2/b -
  Dist[2,Int[Cos[a+b*x]*CosIntegral[a+b*x],x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*SinIntegral[a_.+b_.*x_],x_Symbol] :=
(Print["Int(5th)@TrigIntegralFunctions.m"];
  x^(m+1)*SinIntegral[a+b*x]/(m+1) -
  Dist[b/(m+1),Int[x^(m+1)*Sin[a+b*x]/(a+b*x),x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*CosIntegral[a_.+b_.*x_],x_Symbol] :=
(Print["Int(6th)@TrigIntegralFunctions.m"];
  x^(m+1)*CosIntegral[a+b*x]/(m+1) -
  Dist[b/(m+1),Int[x^(m+1)*Cos[a+b*x]/(a+b*x),x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*SinIntegral[b_.*x_]^2,x_Symbol] :=
(Print["Int(7th)@TrigIntegralFunctions.m"];
  x^(m+1)*SinIntegral[b*x]^2/(m+1) -
  Dist[2/(m+1),Int[x^m*Sin[b*x]*SinIntegral[b*x],x]]) /;
FreeQ[b,x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*CosIntegral[b_.*x_]^2,x_Symbol] :=
(Print["Int(8th)@TrigIntegralFunctions.m"];
  x^(m+1)*CosIntegral[b*x]^2/(m+1) -
  Dist[2/(m+1),Int[x^m*Cos[b*x]*CosIntegral[b*x],x]]) /;
FreeQ[b,x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*SinIntegral[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(9th)@TrigIntegralFunctions.m"];
  x^(m+1)*SinIntegral[a+b*x]^2/(m+1) +
  a*x^m*SinIntegral[a+b*x]^2/(b*(m+1)) -
  Dist[2/(m+1),Int[x^m*Sin[a+b*x]*SinIntegral[a+b*x],x]] -
  Dist[a*m/(b*(m+1)),Int[x^(m-1)*SinIntegral[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*CosIntegral[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(10th)@TrigIntegralFunctions.m"];
  x^(m+1)*CosIntegral[a+b*x]^2/(m+1) +
  a*x^m*CosIntegral[a+b*x]^2/(b*(m+1)) -
  Dist[2/(m+1),Int[x^m*Cos[a+b*x]*CosIntegral[a+b*x],x]] -
  Dist[a*m/(b*(m+1)),Int[x^(m-1)*CosIntegral[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
(* Int[x_^m_.*SinIntegral[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(11th)@TrigIntegralFunctions.m"];
  b*x^(m+2)*SinIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*SinIntegral[a+b*x]^2/(m+1) -
  Dist[2*b/(a*(m+1)),Int[x^(m+1)*Sin[a+b*x]*SinIntegral[a+b*x],x]] -
  Dist[b*(m+2)/(a*(m+1)),Int[x^(m+1)*SinIntegral[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)

(* ::Code:: *)
(* Int[x_^m_.*CosIntegral[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(12th)@TrigIntegralFunctions.m"];
  b*x^(m+2)*CosIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*CosIntegral[a+b*x]^2/(m+1) -
  Dist[2*b/(a*(m+1)),Int[x^(m+1)*Cos[a+b*x]*CosIntegral[a+b*x],x]] -
  Dist[b*(m+2)/(a*(m+1)),Int[x^(m+1)*CosIntegral[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(13th)@TrigIntegralFunctions.m"];
  -Cos[a+b*x]*SinIntegral[c+d*x]/b +
  Dist[d/b,Int[Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(14th)@TrigIntegralFunctions.m"];
  Sin[a+b*x]*CosIntegral[c+d*x]/b -
  Dist[d/b,Int[Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[x_^m_.*Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(15th)@TrigIntegralFunctions.m"];
  -x^m*Cos[a+b*x]*SinIntegral[c+d*x]/b +
  Dist[d/b,Int[x^m*Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x]] +
  Dist[m/b,Int[x^(m-1)*Cos[a+b*x]*SinIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(16th)@TrigIntegralFunctions.m"];
  x^m*Sin[a+b*x]*CosIntegral[c+d*x]/b -
  Dist[d/b,Int[x^m*Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x]] -
  Dist[m/b,Int[x^(m-1)*Sin[a+b*x]*CosIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_*Sin[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(17th)@TrigIntegralFunctions.m"];
  x^(m+1)*Sin[a+b*x]*SinIntegral[c+d*x]/(m+1) -
  Dist[d/(m+1),Int[x^(m+1)*Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x]] -
  Dist[b/(m+1),Int[x^(m+1)*Cos[a+b*x]*SinIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1

(* ::Code:: *)
Int[x_^m_.*Cos[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(18th)@TrigIntegralFunctions.m"];
  x^(m+1)*Cos[a+b*x]*CosIntegral[c+d*x]/(m+1) -
  Dist[d/(m+1),Int[x^(m+1)*Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x]] +
  Dist[b/(m+1),Int[x^(m+1)*Sin[a+b*x]*CosIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(19th)@TrigIntegralFunctions.m"];
  Sin[a+b*x]*SinIntegral[c+d*x]/b -
  Dist[d/b,Int[Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(20th)@TrigIntegralFunctions.m"];
  -Cos[a+b*x]*CosIntegral[c+d*x]/b +
  Dist[d/b,Int[Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[x_^m_.*Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(21th)@TrigIntegralFunctions.m"];
  x^m*Sin[a+b*x]*SinIntegral[c+d*x]/b -
  Dist[d/b,Int[x^m*Sin[a+b*x]*Sin[c+d*x]/(c+d*x),x]] -
  Dist[m/b,Int[x^(m-1)*Sin[a+b*x]*SinIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(22th)@TrigIntegralFunctions.m"];
  -x^m*Cos[a+b*x]*CosIntegral[c+d*x]/b +
  Dist[d/b,Int[x^m*Cos[a+b*x]*Cos[c+d*x]/(c+d*x),x]] +
  Dist[m/b,Int[x^(m-1)*Cos[a+b*x]*CosIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Cos[a_.+b_.*x_]*SinIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(23th)@TrigIntegralFunctions.m"];
  x^(m+1)*Cos[a+b*x]*SinIntegral[c+d*x]/(m+1) -
  Dist[d/(m+1),Int[x^(m+1)*Cos[a+b*x]*Sin[c+d*x]/(c+d*x),x]] +
  Dist[b/(m+1),Int[x^(m+1)*Sin[a+b*x]*SinIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1

(* ::Code:: *)
Int[x_^m_*Sin[a_.+b_.*x_]*CosIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(24th)@TrigIntegralFunctions.m"];
  x^(m+1)*Sin[a+b*x]*CosIntegral[c+d*x]/(m+1) -
  Dist[d/(m+1),Int[x^(m+1)*Sin[a+b*x]*Cos[c+d*x]/(c+d*x),x]] -
  Dist[b/(m+1),Int[x^(m+1)*Cos[a+b*x]*CosIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1

