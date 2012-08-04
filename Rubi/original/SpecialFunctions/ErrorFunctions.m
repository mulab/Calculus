(* ::Package:: *)

(* ::Code:: *)
Int[Erf[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@ErrorFunctions.m"];
  (a+b*x)*Erf[a+b*x]/b + 1/(b*Sqrt[Pi]*E^(a+b*x)^2)) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Erf[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(2th)@ErrorFunctions.m"];
  (a+b*x)*Erf[a+b*x]^2/b -
  Dist[4/Sqrt[Pi],Int[(a+b*x)*Erf[a+b*x]/E^(a+b*x)^2,x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*Erf[a_.+b_.*x_],x_Symbol] :=
(Print["Int(3th)@ErrorFunctions.m"];
  x^(m+1)*Erf[a+b*x]/(m+1) -
  Dist[2*b/(Sqrt[Pi]*(m+1)),Int[x^(m+1)/E^(a+b*x)^2,x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*Erf[b_.*x_]^2,x_Symbol] :=
(Print["Int(4th)@ErrorFunctions.m"];
  x^(m+1)*Erf[b*x]^2/(m+1) -
  Dist[4*b/(Sqrt[Pi]*(m+1)),Int[x^(m+1)*E^(-b^2*x^2)*Erf[b*x],x]]) /;
FreeQ[b,x] && IntegerQ[m] && m+1!=0 && (m>0 || OddQ[m])

(* ::Code:: *)
Int[x_^m_.*Erf[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(5th)@ErrorFunctions.m"];
  Dist[1/b,Subst[Int[(-a/b+x/b)^m*Erf[x]^2,x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_*E^(c_.*x_^2)*Erf[b_.*x_],x_Symbol] :=
(Print["Int(6th)@ErrorFunctions.m"];
  -E^(-b^2*x^2)*Erf[b*x]/(2*b^2) +
  Dist[1/(b*Sqrt[Pi]),Int[E^(-2*b^2*x^2),x]]) /;
FreeQ[{b,c},x] && ZeroQ[c+b^2]

(* ::Code:: *)
Int[x_^m_*E^(c_.*x_^2)*Erf[b_.*x_],x_Symbol] :=
(Print["Int(7th)@ErrorFunctions.m"];
  -x^(m-1)*E^(-b^2*x^2)*Erf[b*x]/(2*b^2) +
  Dist[1/(b*Sqrt[Pi]),Int[x^(m-1)*E^(-2*b^2*x^2),x]] +
  Dist[(m-1)/(2*b^2),Int[x^(m-2)*E^(-b^2*x^2)*Erf[b*x],x]]) /;
FreeQ[{b,c},x] && ZeroQ[c+b^2] && IntegerQ[m] && m>1

(* ::Code:: *)
Int[x_^m_*E^(c_.*x_^2)*Erf[b_.*x_],x_Symbol] :=
(Print["Int(8th)@ErrorFunctions.m"];
  x^(m+1)*E^(-b^2*x^2)*Erf[b*x]/(m+1) -
  Dist[2*b/(Sqrt[Pi]*(m+1)),Int[x^(m+1)*E^(-2*b^2*x^2),x]] +
  Dist[2*b^2/(m+1),Int[x^(m+2)*E^(-b^2*x^2)*Erf[b*x],x]]) /;
FreeQ[{b,c},x] && ZeroQ[c+b^2] && EvenQ[m] && m<-1

(* ::Code:: *)
Int[Erfc[a_.+b_.*x_],x_Symbol] :=
(Print["Int(9th)@ErrorFunctions.m"];
  (a+b*x)*Erfc[a+b*x]/b - 1/(b*Sqrt[Pi]*E^(a+b*x)^2)) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Erfc[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(10th)@ErrorFunctions.m"];
  (a+b*x)*Erfc[a+b*x]^2/b +
  Dist[4/Sqrt[Pi],Int[(a+b*x)*Erfc[a+b*x]/E^(a+b*x)^2,x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*Erfc[a_.+b_.*x_],x_Symbol] :=
(Print["Int(11th)@ErrorFunctions.m"];
  x^(m+1)*Erfc[a+b*x]/(m+1) +
  Dist[2*b/(Sqrt[Pi]*(m+1)),Int[x^(m+1)/E^(a+b*x)^2,x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*Erfc[b_.*x_]^2,x_Symbol] :=
(Print["Int(12th)@ErrorFunctions.m"];
  x^(m+1)*Erfc[b*x]^2/(m+1) +
  Dist[4*b/(Sqrt[Pi]*(m+1)),Int[x^(m+1)*E^(-b^2*x^2)*Erfc[b*x],x]]) /;
FreeQ[b,x] && IntegerQ[m] && m+1!=0 && (m>0 || OddQ[m])

(* ::Code:: *)
Int[x_^m_.*Erfc[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(13th)@ErrorFunctions.m"];
  Dist[1/b,Subst[Int[(-a/b+x/b)^m*Erfc[x]^2,x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_*E^(c_.*x_^2)*Erfc[b_.*x_],x_Symbol] :=
(Print["Int(14th)@ErrorFunctions.m"];
  -E^(-b^2*x^2)*Erfc[b*x]/(2*b^2) -
  Dist[1/(b*Sqrt[Pi]),Int[E^(-2*b^2*x^2),x]]) /;
FreeQ[{b,c},x] && ZeroQ[c+b^2]

(* ::Code:: *)
Int[x_^m_*E^(c_.*x_^2)*Erfc[b_.*x_],x_Symbol] :=
(Print["Int(15th)@ErrorFunctions.m"];
  -x^(m-1)*E^(-b^2*x^2)*Erfc[b*x]/(2*b^2) -
  Dist[1/(b*Sqrt[Pi]),Int[x^(m-1)*E^(-2*b^2*x^2),x]] +
  Dist[(m-1)/(2*b^2),Int[x^(m-2)*E^(-b^2*x^2)*Erfc[b*x],x]]) /;
FreeQ[{b,c},x] && ZeroQ[c+b^2] && IntegerQ[m] && m>1

(* ::Code:: *)
Int[x_^m_*E^(c_.*x_^2)*Erfc[b_.*x_],x_Symbol] :=
(Print["Int(16th)@ErrorFunctions.m"];
  x^(m+1)*E^(-b^2*x^2)*Erfc[b*x]/(m+1) +
  Dist[2*b/(Sqrt[Pi]*(m+1)),Int[x^(m+1)*E^(-2*b^2*x^2),x]] +
  Dist[2*b^2/(m+1),Int[x^(m+2)*E^(-b^2*x^2)*Erfc[b*x],x]]) /;
FreeQ[{b,c},x] && ZeroQ[c+b^2] && EvenQ[m] && m<-1

(* ::Code:: *)
Int[Erfi[a_.+b_.*x_],x_Symbol] :=
(Print["Int(17th)@ErrorFunctions.m"];
  (a+b*x)*Erfi[a+b*x]/b - E^(a+b*x)^2/(b*Sqrt[Pi])) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Erfi[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(18th)@ErrorFunctions.m"];
  (a+b*x)*Erfi[a+b*x]^2/b -
  Dist[4/Sqrt[Pi],Int[(a+b*x)*E^(a+b*x)^2*Erfi[a+b*x],x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*Erfi[a_.+b_.*x_],x_Symbol] :=
(Print["Int(19th)@ErrorFunctions.m"];
  x^(m+1)*Erfi[a+b*x]/(m+1) -
  Dist[2*b/(Sqrt[Pi]*(m+1)),Int[x^(m+1)*E^(a+b*x)^2,x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*Erfi[b_.*x_]^2,x_Symbol] :=
(Print["Int(20th)@ErrorFunctions.m"];
  x^(m+1)*Erfi[b*x]^2/(m+1) -
  Dist[4*b/(Sqrt[Pi]*(m+1)),Int[x^(m+1)*E^(b^2*x^2)*Erfi[b*x],x]]) /;
FreeQ[b,x] && IntegerQ[m] && m+1!=0 && (m>0 || OddQ[m])

(* ::Code:: *)
Int[x_^m_.*Erfi[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(21th)@ErrorFunctions.m"];
  Dist[1/b,Subst[Int[(-a/b+x/b)^m*Erfi[x]^2,x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_*E^(c_.*x_^2)*Erfi[b_.*x_],x_Symbol] :=
(Print["Int(22th)@ErrorFunctions.m"];
  E^(b^2*x^2)*Erfi[b*x]/(2*b^2) -
  Dist[1/(b*Sqrt[Pi]),Int[E^(2*b^2*x^2),x]]) /;
FreeQ[{b,c},x] && ZeroQ[c-b^2]

(* ::Code:: *)
Int[x_^m_*E^(c_.*x_^2)*Erfi[b_.*x_],x_Symbol] :=
(Print["Int(23th)@ErrorFunctions.m"];
  x^(m-1)*E^(b^2*x^2)*Erfi[b*x]/(2*b^2) -
  Dist[1/(b*Sqrt[Pi]),Int[x^(m-1)*E^(2*b^2*x^2),x]] -
  Dist[(m-1)/(2*b^2),Int[x^(m-2)*E^(b^2*x^2)*Erfi[b*x],x]]) /;
FreeQ[{b,c},x] && ZeroQ[c-b^2] && IntegerQ[m] && m>1

(* ::Code:: *)
Int[x_^m_*E^(c_.*x_^2)*Erfi[b_.*x_],x_Symbol] :=
(Print["Int(24th)@ErrorFunctions.m"];
  x^(m+1)*E^(b^2*x^2)*Erfi[b*x]/(m+1) -
  Dist[2*b/(Sqrt[Pi]*(m+1)),Int[x^(m+1)*E^(2*b^2*x^2),x]] -
  Dist[2*b^2/(m+1),Int[x^(m+2)*E^(b^2*x^2)*Erfi[b*x],x]]) /;
FreeQ[{b,c},x] && ZeroQ[c-b^2] && EvenQ[m] && m<-1

