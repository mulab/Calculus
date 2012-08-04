(* ::Package:: *)

(* ::Code:: *)
Int[SinhIntegral[a_.+b_.*x_],x_Symbol] :=
  (a+b*x)*SinhIntegral[a+b*x]/b - Cosh[a+b*x]/b/;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[CoshIntegral[a_.+b_.*x_],x_Symbol] :=
(Print["Int(2th)@HyperbolicIntegralFunctions.m"];
  (a+b*x)*CoshIntegral[a+b*x]/b - Sinh[a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[SinhIntegral[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(3th)@HyperbolicIntegralFunctions.m"];
  (a+b*x)*SinhIntegral[a+b*x]^2/b -
  Dist[2,Int[Sinh[a+b*x]*SinhIntegral[a+b*x],x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[CoshIntegral[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(4th)@HyperbolicIntegralFunctions.m"];
  (a+b*x)*CoshIntegral[a+b*x]^2/b -
  Dist[2,Int[Cosh[a+b*x]*CoshIntegral[a+b*x],x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*SinhIntegral[a_.+b_.*x_],x_Symbol] :=
(Print["Int(5th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*SinhIntegral[a+b*x]/(m+1) -
  Dist[b/(m+1),Int[x^(m+1)*Sinh[a+b*x]/(a+b*x),x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*CoshIntegral[a_.+b_.*x_],x_Symbol] :=
(Print["Int(6th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*CoshIntegral[a+b*x]/(m+1) -
  Dist[b/(m+1),Int[x^(m+1)*Cosh[a+b*x]/(a+b*x),x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*SinhIntegral[b_.*x_]^2,x_Symbol] :=
(Print["Int(7th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*SinhIntegral[b*x]^2/(m+1) -
  Dist[2/(m+1),Int[x^m*Sinh[b*x]*SinhIntegral[b*x],x]]) /;
FreeQ[b,x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*CoshIntegral[b_.*x_]^2,x_Symbol] :=
(Print["Int(8th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*CoshIntegral[b*x]^2/(m+1) -
  Dist[2/(m+1),Int[x^m*Cosh[b*x]*CoshIntegral[b*x],x]]) /;
FreeQ[b,x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*SinhIntegral[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(9th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*SinhIntegral[a+b*x]^2/(m+1) +
  a*x^m*SinhIntegral[a+b*x]^2/(b*(m+1)) -
  Dist[2/(m+1),Int[x^m*Sinh[a+b*x]*SinhIntegral[a+b*x],x]] -
  Dist[a*m/(b*(m+1)),Int[x^(m-1)*SinhIntegral[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*CoshIntegral[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(10th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*CoshIntegral[a+b*x]^2/(m+1) +
  a*x^m*CoshIntegral[a+b*x]^2/(b*(m+1)) -
  Dist[2/(m+1),Int[x^m*Cosh[a+b*x]*CoshIntegral[a+b*x],x]] -
  Dist[a*m/(b*(m+1)),Int[x^(m-1)*CoshIntegral[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
(* Int[x_^m_.*SinhIntegral[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(11th)@HyperbolicIntegralFunctions.m"];
  b*x^(m+2)*SinhIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*SinhIntegral[a+b*x]^2/(m+1) -
  Dist[2*b/(a*(m+1)),Int[x^(m+1)*Sinh[a+b*x]*SinhIntegral[a+b*x],x]] -
  Dist[b*(m+2)/(a*(m+1)),Int[x^(m+1)*SinhIntegral[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)

(* ::Code:: *)
(* Int[x_^m_.*CoshIntegral[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(12th)@HyperbolicIntegralFunctions.m"];
  b*x^(m+2)*CoshIntegral[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*CoshIntegral[a+b*x]^2/(m+1) -
  Dist[2*b/(a*(m+1)),Int[x^(m+1)*Cosh[a+b*x]*CoshIntegral[a+b*x],x]] -
  Dist[b*(m+2)/(a*(m+1)),Int[x^(m+1)*CoshIntegral[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)

(* ::Code:: *)
Int[Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(13th)@HyperbolicIntegralFunctions.m"];
  Cosh[a+b*x]*SinhIntegral[c+d*x]/b -
  Dist[d/b,Int[Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(14th)@HyperbolicIntegralFunctions.m"];
  Sinh[a+b*x]*CoshIntegral[c+d*x]/b -
  Dist[d/b,Int[Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(15th)@HyperbolicIntegralFunctions.m"];
  x^m*Cosh[a+b*x]*SinhIntegral[c+d*x]/b -
  Dist[d/b,Int[x^m*Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x]] -
  Dist[m/b,Int[x^(m-1)*Cosh[a+b*x]*SinhIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(16th)@HyperbolicIntegralFunctions.m"];
  x^m*Sinh[a+b*x]*CoshIntegral[c+d*x]/b -
  Dist[d/b,Int[x^m*Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x]] -
  Dist[m/b,Int[x^(m-1)*Sinh[a+b*x]*CoshIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_*Sinh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(17th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*Sinh[a+b*x]*SinhIntegral[c+d*x]/(m+1) -
  Dist[d/(m+1),Int[x^(m+1)*Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x]] -
  Dist[b/(m+1),Int[x^(m+1)*Cosh[a+b*x]*SinhIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(18th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*Cosh[a+b*x]*CoshIntegral[c+d*x]/(m+1) -
  Dist[d/(m+1),Int[x^(m+1)*Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x]] -
  Dist[b/(m+1),Int[x^(m+1)*Sinh[a+b*x]*CoshIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1

(* ::Code:: *)
Int[Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(19th)@HyperbolicIntegralFunctions.m"];
  Sinh[a+b*x]*SinhIntegral[c+d*x]/b -
  Dist[d/b,Int[Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(20th)@HyperbolicIntegralFunctions.m"];
  Cosh[a+b*x]*CoshIntegral[c+d*x]/b -
  Dist[d/b,Int[Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(21th)@HyperbolicIntegralFunctions.m"];
  x^m*Sinh[a+b*x]*SinhIntegral[c+d*x]/b -
  Dist[d/b,Int[x^m*Sinh[a+b*x]*Sinh[c+d*x]/(c+d*x),x]] -
  Dist[m/b,Int[x^(m-1)*Sinh[a+b*x]*SinhIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(22th)@HyperbolicIntegralFunctions.m"];
  x^m*Cosh[a+b*x]*CoshIntegral[c+d*x]/b -
  Dist[d/b,Int[x^m*Cosh[a+b*x]*Cosh[c+d*x]/(c+d*x),x]] -
  Dist[m/b,Int[x^(m-1)*Cosh[a+b*x]*CoshIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_]*SinhIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(23th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*Cosh[a+b*x]*SinhIntegral[c+d*x]/(m+1) -
  Dist[d/(m+1),Int[x^(m+1)*Cosh[a+b*x]*Sinh[c+d*x]/(c+d*x),x]] -
  Dist[b/(m+1),Int[x^(m+1)*Sinh[a+b*x]*SinhIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1

(* ::Code:: *)
Int[x_^m_*Sinh[a_.+b_.*x_]*CoshIntegral[c_.+d_.*x_],x_Symbol] :=
(Print["Int(24th)@HyperbolicIntegralFunctions.m"];
  x^(m+1)*Sinh[a+b*x]*CoshIntegral[c+d*x]/(m+1) -
  Dist[d/(m+1),Int[x^(m+1)*Sinh[a+b*x]*Cosh[c+d*x]/(c+d*x),x]] -
  Dist[b/(m+1),Int[x^(m+1)*Cosh[a+b*x]*CoshIntegral[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1

