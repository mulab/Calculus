(* ::Package:: *)

(* ::Code:: *)
Int[ExpIntegralE[n_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@ExponentialIntegralFunctions.m"];
  -ExpIntegralE[n+1,a+b*x]/b) /;
FreeQ[{a,b,n},x]

(* ::Code:: *)
Int[x_^m_.*ExpIntegralE[n_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(2th)@ExponentialIntegralFunctions.m"];
  x^(m+1)*ExpIntegralE[n,a+b*x]/(m+1) +
  Dist[b/(m+1),Int[x^(m+1)*ExpIntegralE[n-1,a+b*x],x]]) /;
FreeQ[{a,b,m},x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_.*ExpIntegralE[n_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(3th)@ExponentialIntegralFunctions.m"];
  -x^m*ExpIntegralE[n+1,a+b*x]/b +
  Dist[m/b,Int[x^(m-1)*ExpIntegralE[n+1,a+b*x],x]]) /;
FreeQ[{a,b,m},x] && IntegerQ[n] && n<0

(* ::Code:: *)
Int[ExpIntegralEi[a_.+b_.*x_],x_Symbol] :=
(Print["Int(4th)@ExponentialIntegralFunctions.m"];
  (a+b*x)*ExpIntegralEi[a+b*x]/b - E^(a+b*x)/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[ExpIntegralEi[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(5th)@ExponentialIntegralFunctions.m"];
  (a+b*x)*ExpIntegralEi[a+b*x]^2/b -
  Dist[2,Int[E^(a+b*x)*ExpIntegralEi[a+b*x],x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*ExpIntegralEi[a_.+b_.*x_],x_Symbol] :=
(Print["Int(6th)@ExponentialIntegralFunctions.m"];
  x^(m+1)*ExpIntegralEi[a+b*x]/(m+1) -
  Dist[b/(m+1),Int[x^(m+1)*E^(a+b*x)/(a+b*x),x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*ExpIntegralEi[b_.*x_]^2,x_Symbol] :=
(Print["Int(7th)@ExponentialIntegralFunctions.m"];
  x^(m+1)*ExpIntegralEi[b*x]^2/(m+1) -
  Dist[2/(m+1),Int[x^m*E^(b*x)*ExpIntegralEi[b*x],x]]) /;
FreeQ[b,x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*ExpIntegralEi[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(8th)@ExponentialIntegralFunctions.m"];
  x^(m+1)*ExpIntegralEi[a+b*x]^2/(m+1) +
  a*x^m*ExpIntegralEi[a+b*x]^2/(b*(m+1)) -
  Dist[2/(m+1),Int[x^m*E^(a+b*x)*ExpIntegralEi[a+b*x],x]] -
  Dist[a*m/(b*(m+1)),Int[x^(m-1)*ExpIntegralEi[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
(* Int[x_^m_.*ExpIntegralEi[a_+b_.*x_]^2,x_Symbol] :=
(Print["Int(9th)@ExponentialIntegralFunctions.m"];
  b*x^(m+2)*ExpIntegralEi[a+b*x]^2/(a*(m+1)) +
  x^(m+1)*ExpIntegralEi[a+b*x]^2/(m+1) -
  Dist[2*b/(a*(m+1)),Int[x^(m+1)*E^(a+b*x)*ExpIntegralEi[a+b*x],x]] -
  Dist[b*(m+2)/(a*(m+1)),Int[x^(m+1)*ExpIntegralEi[a+b*x]^2,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-2 *)

(* ::Code:: *)
Int[E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
(Print["Int(10th)@ExponentialIntegralFunctions.m"];
  E^(a+b*x)*ExpIntegralEi[c+d*x]/b -
  Dist[d/b,Int[E^(a+b*x)*E^(c+d*x)/(c+d*x),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[x_^m_.*E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
(Print["Int(11th)@ExponentialIntegralFunctions.m"];
  x^m*E^(a+b*x)*ExpIntegralEi[c+d*x]/b -
  Dist[d/b,Int[x^m*E^(a+b*x)*E^(c+d*x)/(c+d*x),x]] -
  Dist[m/b,Int[x^(m-1)*E^(a+b*x)*ExpIntegralEi[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_*E^(a_.+b_.*x_)*ExpIntegralEi[c_.+d_.*x_],x_Symbol] :=
(Print["Int(12th)@ExponentialIntegralFunctions.m"];
  x^(m+1)*E^(a+b*x)*ExpIntegralEi[c+d*x]/(m+1) -
  Dist[d/(m+1),Int[x^(m+1)*E^(a+b*x)*E^(c+d*x)/(c+d*x),x]] -
  Dist[b/(m+1),Int[x^(m+1)*E^(a+b*x)*ExpIntegralEi[c+d*x],x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m<-1

