(* ::Package:: *)

(* ::Code:: *)
Int[ArcSech[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@InverseHyperbolicSecantFunctions.m"];
  (a+b*x)*ArcSech[a+b*x]/b - 2*ArcTan[Sqrt[(1-a-b*x)/(1+a+b*x)]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*ArcSech[a_+b_.*x_],x_Symbol] :=
(Print["Int(2th)@InverseHyperbolicSecantFunctions.m"];
  Dist[1/b,Subst[Int[(-a/b+x/b)^m*ArcSech[x],x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*ArcSech[a_.*x_],x_Symbol] :=
(Print["Int(3th)@InverseHyperbolicSecantFunctions.m"];
  x^(m+1)*ArcSech[a*x]/(m+1) + 
  Dist[1/(m+1),Int[x^m/(Sqrt[(1-a*x)/(1+a*x)]*(1+a*x)),x]]) /;
FreeQ[{a,m},x] && NonzeroQ[m+1]

(* Int[ArcSech[a_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(4th)@InverseHyperbolicSecantFunctions.m"];

  -ArcSech[a*x^n]^2/(2*n) - 
  ArcSech[a*x^n]*Log[1+E^(-2*ArcSech[a*x^n])]/n + 
  PolyLog[2,-E^(-2*ArcSech[a*x^n])]/(2*n)) /;
(* -ArcSech[a*x^n]^2/(2*n) - 
  ArcSech[a*x^n]*Log[1+1/(1/(a*x^n)+Sqrt[-1+1/(a*x^n)]*Sqrt[1+1/(a*x^n)])^2]/n + 
  PolyLog[2,-1/(1/(a*x^n)+Sqrt[-1+1/(a*x^n)]*Sqrt[1+1/(a*x^n)])^2]/(2*n) /; *)
FreeQ[{a,n},x] *)

(* ::Code:: *)
Int[u_.*ArcSech[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
(Print["Int(5th)@InverseHyperbolicSecantFunctions.m"];
  Int[u*ArcCosh[a/c+b*x^n/c]^m,x]) /;
FreeQ[{a,b,c,n,m},x]

(* ::Code:: *)
(* Int[ArcSech[u_],x_Symbol] :=
(Print["Int(6th)@InverseHyperbolicSecantFunctions.m"];
  x*ArcSech[u] +
  Int[Regularize[x*D[u,x]/(u^2*Sqrt[-1+1/u]*Sqrt[1+1/u]),x],x]) /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialOfLinear[u,x]] *)

(* ::Code:: *)
Int[E^(n_.*ArcSech[u_]), x_Symbol] :=
(Print["Int(7th)@InverseHyperbolicSecantFunctions.m"];
  Int[(1/u + Sqrt[(1-u)/(1+u)] + Sqrt[(1-u)/(1+u)]/u)^n,x]) /;
IntegerQ[n] && PolynomialQ[u,x]

(* ::Code:: *)
Int[x_^m_.*E^(n_.*ArcSech[u_]), x_Symbol] :=
(Print["Int(8th)@InverseHyperbolicSecantFunctions.m"];
  Int[x^m*(1/u + Sqrt[(1-u)/(1+u)] + Sqrt[(1-u)/(1+u)]/u)^n,x]) /;
RationalQ[m] && IntegerQ[n] && PolynomialQ[u,x]
