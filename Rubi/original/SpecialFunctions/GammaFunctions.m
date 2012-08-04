(* ::Package:: *)

(* ::Code:: *)
Int[Gamma[n_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@GammaFunctions.m"];
  (a+b*x)*Gamma[n,a+b*x]/b -
  Gamma[n+1,a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*Gamma[n_,a_.*x_],x_Symbol] :=
(Print["Int(2th)@GammaFunctions.m"];
  x^(m+1)*Gamma[n,a*x]/(m+1) -
  Gamma[m+n+1,a*x]/((m+1)*a^(m+1))) /;
FreeQ[{a,n},x] && (IntegerQ[m] || PositiveQ[a])

(* ::Code:: *)
Int[x_^m_.*Gamma[n_,a_*x_],x_Symbol] :=
(Print["Int(3th)@GammaFunctions.m"];
  x^(m+1)*Gamma[n,a*x]/(m+1) -
  x^(m+1)*Gamma[m+n+1,a*x]/((m+1)*(a*x)^(m+1))) /;
FreeQ[{a,m,n},x]

(* ::Code:: *)
Int[x_^m_.*Gamma[n_,a_+b_.*x_],x_Symbol] :=
(Print["Int(4th)@GammaFunctions.m"];
  x^m*(a+b*x)*Gamma[n,a+b*x]/(b*(m+1)) -
  x^m*Gamma[n+1,a+b*x]/(b*(m+1)) -
  Dist[a*m/(b*(m+1)),Int[x^(m-1)*Gamma[n,a+b*x],x]] +
  Dist[m/(b*(m+1)),Int[x^(m-1)*Gamma[n+1,a+b*x],x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[LogGamma[a_.+b_.*x_],x_Symbol] :=
(Print["Int(5th)@GammaFunctions.m"];
  PolyGamma[-2,a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*LogGamma[a_.+b_.*x_],x_Symbol] :=
(Print["Int(6th)@GammaFunctions.m"];
  x^m*PolyGamma[-2,a+b*x]/b -
  Dist[m/b,Int[x^(m-1)*PolyGamma[-2,a+b*x],x]]) /;
FreeQ[{a,b},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(7th)@GammaFunctions.m"];
  PolyGamma[n-1,a+b*x]/b) /;
FreeQ[{a,b,n},x]

(* ::Code:: *)
Int[x_^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(8th)@GammaFunctions.m"];
  x^m*PolyGamma[n-1,a+b*x]/b -
  Dist[m/b,Int[x^(m-1)*PolyGamma[n-1,a+b*x],x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*PolyGamma[n_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(9th)@GammaFunctions.m"];
  x^(m+1)*PolyGamma[n,a+b*x]/(m+1) -
  Dist[b/(m+1),Int[x^(m+1)*PolyGamma[n+1,a+b*x],x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1

(* ::Code:: *)
Int[Gamma[a_.+b_.*x_]^n_.*PolyGamma[0,a_.+b_.*x_],x_Symbol] :=
(Print["Int(10th)@GammaFunctions.m"];
  Gamma[a+b*x]^n/(b*n)) /;
FreeQ[{a,b,n},x]

(* ::Code:: *)
Int[((a_.+b_.*x_)!)^n_.*PolyGamma[0,c_.+b_.*x_],x_Symbol] :=
(Print["Int(11th)@GammaFunctions.m"];
  ((a+b*x)!)^n/(b*n)) /;
FreeQ[{a,b,c,n},x] && ZeroQ[a-c+1]

