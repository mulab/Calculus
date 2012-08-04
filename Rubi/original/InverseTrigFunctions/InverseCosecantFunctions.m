(* ::Package:: *)

(* ::Code:: *)
Int[ArcCsc[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@InverseCosecantFunctions.m"];
  (a+b*x)*ArcCsc[a+b*x]/b +
  Int[1/((a+b*x)*Sqrt[1-1/(a+b*x)^2]),x]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*ArcCsc[a_+b_.*x_],x_Symbol] :=
(Print["Int(2th)@InverseCosecantFunctions.m"];
  Dist[1/b,Subst[Int[(-a/b+x/b)^m*ArcCsc[x],x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*ArcCsc[a_.*x_],x_Symbol] :=
(Print["Int(3th)@InverseCosecantFunctions.m"];
  x^(m+1)*ArcCsc[a*x]/(m+1) +
  Dist[1/(a*(m+1)),Int[x^(m-1)/Sqrt[1-1/(a^2*x^2)],x]]) /;
FreeQ[{a,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*ArcCsc[a_.+b_.*x_],x_Symbol] :=
(Print["Int(4th)@InverseCosecantFunctions.m"];
  x^(m+1)*ArcCsc[a+b*x]/(m+1) +
  Dist[b/(m+1),Int[x^(m+1)/((a+b*x)^2*Sqrt[1-1/(a+b*x)^2]),x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* Int[ArcCsc[a_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(5th)@InverseCosecantFunctions.m"];

  I*ArcCsc[a*x^n]^2/(2*n) - 
  ArcCsc[a*x^n]*Log[1-(I/(x^n*a)+Sqrt[1-1/(x^(2*n)*a^2)])^2]/n + 
  I*PolyLog[2,(I/(x^n*a)+Sqrt[1-1/(x^(2*n)*a^2)])^2]/(2*n)) /;
(* -Sqrt[-1/a^2]*a*ArcCsc[a*x^n]^2/(2*n) - 
  ArcCsc[a*x^n]*Log[2*(1/(x^n*a^2) + Sqrt[-1/a^2]*Sqrt[1-1/(x^(2*n)*a^2)])/x^n]/n - 
  Sqrt[-1/a^2]*a*PolyLog[2, 1-2*(1/(x^n*a^2)+Sqrt[-1/a^2]*Sqrt[1-1/(x^(2*n)*a^2)])/x^n]/(2*n) /; *)
FreeQ[{a,n},x] *)

(* ::Code:: *)
Int[u_.*ArcCsc[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
(Print["Int(6th)@InverseCosecantFunctions.m"];
  Int[u*ArcSin[a/c+b*x^n/c]^m,x]) /;
FreeQ[{a,b,c,n,m},x]

(* ::Code:: *)
Int[ArcCsc[u_],x_Symbol] :=
(Print["Int(7th)@InverseCosecantFunctions.m"];
  x*ArcCsc[u] +
  Int[Regularize[x*D[u,x]/(u^2*Sqrt[1-1/u^2]),x],x]) /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialOfLinear[u,x]]
