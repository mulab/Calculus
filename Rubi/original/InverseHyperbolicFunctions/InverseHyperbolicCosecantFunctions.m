(* ::Package:: *)

(* ::Code:: *)
Int[ArcCsch[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@InverseHyperbolicCosecantFunctions.m"];
  (a+b*x)*ArcCsch[a+b*x]/b + ArcTanh[Sqrt[1+1/(a+b*x)^2]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*ArcCsch[a_+b_.*x_],x_Symbol] :=
(Print["Int(2th)@InverseHyperbolicCosecantFunctions.m"];
  Dist[1/b,Subst[Int[(-a/b+x/b)^m*ArcCsch[x],x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*ArcCsch[a_.+b_.*x_],x_Symbol] :=
(Print["Int(3th)@InverseHyperbolicCosecantFunctions.m"];
  x^(m+1)*ArcCsch[a+b*x]/(m+1) + 
  Dist[b/(m+1),Int[x^(m+1)/((a+b*x)^2*Sqrt[1+1/(a+b*x)^2]),x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* Int[ArcCsch[a_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(4th)@InverseHyperbolicCosecantFunctions.m"];

  -ArcCsch[a*x^n]^2/(2*n) - 
  ArcCsch[a*x^n]*Log[1-E^(-2*ArcCsch[a*x^n])]/n + 
  PolyLog[2,E^(-2*ArcCsch[a*x^n])]/(2*n)) /;
(* -ArcCsch[a*x^n]^2/(2*n) - 
  ArcCsch[a*x^n]*Log[1-1/(1/(a*x^n)+Sqrt[1+1/(a^2*x^(2*n))])^2]/n + 
  PolyLog[2,1/(1/(a*x^n)+Sqrt[1+1/(a^2*x^(2*n))])^2]/(2*n) /; *)
FreeQ[{a,n},x] *)

(* ::Code:: *)
Int[u_.*ArcCsch[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
(Print["Int(5th)@InverseHyperbolicCosecantFunctions.m"];
  Int[u*ArcSinh[a/c+b*x^n/c]^m,x]) /;
FreeQ[{a,b,c,n,m},x]

(* ::Code:: *)
Int[ArcCsch[u_],x_Symbol] :=
(Print["Int(6th)@InverseHyperbolicCosecantFunctions.m"];
  x*ArcCsch[u] +
  Int[Regularize[x*D[u,x]/(u^2*Sqrt[1+1/u^2]),x],x]) /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialOfLinear[u,x]]

(* ::Code:: *)
Int[E^(n_.*ArcCsch[u_]), x_Symbol] :=
(Print["Int(7th)@InverseHyperbolicCosecantFunctions.m"];
  Int[(1/u+Sqrt[1+1/u^2])^n,x]) /;
IntegerQ[n] && PolynomialQ[u,x]

(* ::Code:: *)
Int[x_^m_.*E^(n_.*ArcCsch[u_]), x_Symbol] :=
(Print["Int(8th)@InverseHyperbolicCosecantFunctions.m"];
  Int[x^m*(1/u+Sqrt[1+1/u^2])^n,x]) /;
RationalQ[m] && IntegerQ[n] && PolynomialQ[u,x]
