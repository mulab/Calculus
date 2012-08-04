(* ::Package:: *)

(* ::Code:: *)
Int[ArcSinh[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@InverseHyperbolicSineFunctions.m"];
  (a+b*x)*ArcSinh[a+b*x]/b - Sqrt[1+(a+b*x)^2]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[ArcSinh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(2th)@InverseHyperbolicSineFunctions.m"];
  (a+b*x)*ArcSinh[a+b*x]^n/b -
  n*Sqrt[1+(a+b*x)^2]*ArcSinh[a+b*x]^(n-1)/b +
  Dist[n*(n-1),Int[ArcSinh[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[1/ArcSinh[a_.+b_.*x_],x_Symbol] :=
(Print["Int(3th)@InverseHyperbolicSineFunctions.m"];
  CoshIntegral[ArcSinh[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[1/ArcSinh[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(4th)@InverseHyperbolicSineFunctions.m"];
  -Sqrt[1+(a+b*x)^2]/(b*ArcSinh[a+b*x]) + SinhIntegral[ArcSinh[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[1/Sqrt[ArcSinh[a_.+b_.*x_]],x_Symbol] :=
(Print["Int(5th)@InverseHyperbolicSineFunctions.m"];
  Sqrt[Pi]*Erf[Sqrt[ArcSinh[a+b*x]]]/(2*b) +
  Sqrt[Pi]*Erfi[Sqrt[ArcSinh[a+b*x]]]/(2*b)) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Sqrt[ArcSinh[a_.+b_.*x_]],x_Symbol] :=
(Print["Int(6th)@InverseHyperbolicSineFunctions.m"];
  (a+b*x)*Sqrt[ArcSinh[a+b*x]]/b +
  Sqrt[Pi]*Erf[Sqrt[ArcSinh[a+b*x]]]/(4*b) -
  Sqrt[Pi]*Erfi[Sqrt[ArcSinh[a+b*x]]]/(4*b)) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[ArcSinh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(7th)@InverseHyperbolicSineFunctions.m"];
  -(a+b*x)*ArcSinh[a+b*x]^(n+2)/(b*(n+1)*(n+2)) +
  Sqrt[1+(a+b*x)^2]*ArcSinh[a+b*x]^(n+1)/(b*(n+1)) +
  Dist[1/((n+1)*(n+2)),Int[ArcSinh[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[ArcSinh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(8th)@InverseHyperbolicSineFunctions.m"];
  ArcSinh[a+b*x]^n*Gamma[n+1,-ArcSinh[a+b*x]]/(2*b*(-ArcSinh[a+b*x])^n) -
  Gamma[n+1,ArcSinh[a+b*x]]/(2*b)) /;
FreeQ[{a,b,n},x] && (Not[RationalQ[n]] || -1<n<1)

(* ::Code:: *)
Int[x_^m_.*ArcSinh[a_.+b_.*x_],x_Symbol] :=
(Print["Int(9th)@InverseHyperbolicSineFunctions.m"];
  x^(m+1)*ArcSinh[a+b*x]/(m+1) - 
  Dist[b/(m+1),Int[x^(m+1)/Sqrt[1+a^2+2*a*b*x+b^2*x^2],x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_/Sqrt[ArcSinh[a_.*x_]],x_Symbol] :=
(Print["Int(10th)@InverseHyperbolicSineFunctions.m"];
  -Sqrt[Pi/2]*Erf[Sqrt[2]*Sqrt[ArcSinh[a*x]]]/(4*a^2) + 
  Sqrt[Pi/2]*Erfi[Sqrt[2]*Sqrt[ArcSinh[a*x]]]/(4*a^2)) /;
FreeQ[a,x]

(* ::Code:: *)
Int[x_/ArcSinh[a_.*x_]^(3/2),x_Symbol] :=
(Print["Int(11th)@InverseHyperbolicSineFunctions.m"];
  -2*x*Sqrt[1+a^2*x^2]/(a*Sqrt[ArcSinh[a*x]]) +
  Sqrt[Pi/2]*Erf[Sqrt[2]*Sqrt[ArcSinh[a*x]]]/a^2 +
  Sqrt[Pi/2]*Erfi[Sqrt[2]*Sqrt[ArcSinh[a*x]]]/a^2) /;
FreeQ[a,x]

(* ::Code:: *)
Int[x_*ArcSinh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(12th)@InverseHyperbolicSineFunctions.m"];
  -n*x*Sqrt[1+a^2*x^2]*ArcSinh[a*x]^(n-1)/(4*a) +
  ArcSinh[a*x]^n/(4*a^2) + x^2*ArcSinh[a*x]^n/2 +
  Dist[n*(n-1)/4,Int[x*ArcSinh[a*x]^(n-2),x]]) /;
FreeQ[a,x] && RationalQ[n] && n>0

(* ::Code:: *)
Int[x_*ArcSinh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(13th)@InverseHyperbolicSineFunctions.m"];
  x*Sqrt[1+a^2*x^2]*ArcSinh[a*x]^(n+1)/(a*(n+1)) -
  ArcSinh[a*x]^(n+2)/(a^2*(n+1)*(n+2)) -
  2*x^2*ArcSinh[a*x]^(n+2)/((n+1)*(n+2)) +
  Dist[4/((n+1)*(n+2)),Int[x*ArcSinh[a*x]^(n+2),x]]) /;
FreeQ[a,x] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[ArcSinh[a_.*x_]^n_/x_^3,x_Symbol] :=
(Print["Int(14th)@InverseHyperbolicSineFunctions.m"];
  -a*n*Sqrt[1+a^2*x^2]*ArcSinh[a*x]^(n-1)/(2*x) -
  ArcSinh[a*x]^n/(2*x^2) +
  Dist[a^2*n*(n-1)/2,Int[ArcSinh[a*x]^(n-2)/x,x]]) /;
FreeQ[a,x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[x_^m_*ArcSinh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(15th)@InverseHyperbolicSineFunctions.m"];
  -a*n*x^(m+2)*Sqrt[1+a^2*x^2]*ArcSinh[a*x]^(n-1)/((m+1)*(m+2)) +
  x^(m+1)*ArcSinh[a*x]^n/(m+1) +
  a^2*(m+3)*x^(m+3)*ArcSinh[a*x]^n/((m+1)*(m+2)) -
  Dist[a^2*(m+3)^2/((m+1)*(m+2)),Int[x^(m+2)*ArcSinh[a*x]^n,x]] +
  Dist[a^2*n*(n-1)/((m+1)*(m+2)),Int[x^(m+2)*ArcSinh[a*x]^(n-2),x]]) /;
FreeQ[a,x] && IntegerQ[m] && RationalQ[n] && m<-3 && n>1

(* ::Code:: *)
Int[x_^m_*ArcSinh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(16th)@InverseHyperbolicSineFunctions.m"];
  x^m*Sqrt[1+a^2*x^2]*ArcSinh[a*x]^(n+1)/(a*(n+1)) -
  m*x^(m-1)*ArcSinh[a*x]^(n+2)/(a^2*(n+1)*(n+2)) -
  (m+1)*x^(m+1)*ArcSinh[a*x]^(n+2)/((n+1)*(n+2)) +
  Dist[(m+1)^2/((n+1)*(n+2)),Int[x^m*ArcSinh[a*x]^(n+2),x]] +
  Dist[m*(m-1)/(a^2*(n+1)*(n+2)),Int[x^(m-2)*ArcSinh[a*x]^(n+2),x]]) /;
FreeQ[a,x] && IntegerQ[m] && RationalQ[n] && m>1 && n<-1 && n!=-2

(* ::Code:: *)
Int[ArcSinh[a_.*x_^p_.]^n_./x_,x_Symbol] :=
(Print["Int(17th)@InverseHyperbolicSineFunctions.m"];
  Dist[1/p,Subst[Int[x^n*Coth[x],x],x,ArcSinh[a*x^p]]]) /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_.*ArcSinh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(18th)@InverseHyperbolicSineFunctions.m"];
  x^(m+1)*ArcSinh[a*x]^n/(m+1) -
  Dist[n/(a^(m+1)*(m+1)),Subst[Int[x^(n-1)*Sinh[x]^(m+1),x],x,ArcSinh[a*x]]]) /;
FreeQ[{a,n},x] && IntegerQ[m] && m!=-1

(* ::Code:: *)
Int[(a_+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(19th)@InverseHyperbolicSineFunctions.m"];
  Dist[1/d,Subst[Int[(a+b*x)^n*Cosh[x],x],x,ArcSinh[c+d*x]]]) /;
FreeQ[{a,b,c,d},x] && Not[IntegerQ[n]]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*ArcSinh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(20th)@InverseHyperbolicSineFunctions.m"];
  Dist[1/d^(m+1),Subst[Int[(a+b*x)^n*(Sinh[x]-c)^m*Cosh[x],x],x,ArcSinh[c+d*x]]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && Not[IntegerQ[n]] && m>0

(* ::Code:: *)
Int[x_*ArcSinh[a_.+b_.*x_]^n_/Sqrt[u_],x_Symbol] :=
(Print["Int(21th)@InverseHyperbolicSineFunctions.m"];
  Sqrt[u]*ArcSinh[a+b*x]^n/b^2 -
  Dist[n/b,Int[ArcSinh[a+b*x]^(n-1),x]] -
  Dist[a/b,Int[ArcSinh[a+b*x]^n/Sqrt[u],x]]) /;
FreeQ[{a,b},x] && ZeroQ[u-1-(a+b*x)^2] && RationalQ[n] && n>1

(* ::Code:: *)
Int[u_.*ArcSinh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
(Print["Int(22th)@InverseHyperbolicSineFunctions.m"];
  Int[u*ArcCsch[a/c+b*x^n/c]^m,x]) /;
FreeQ[{a,b,c,n,m},x]

(* ::Code:: *)
Int[f_^(c_.*ArcSinh[a_.+b_.*x_]),x_Symbol] :=
(Print["Int(23th)@InverseHyperbolicSineFunctions.m"];
  f^(c*ArcSinh[a+b*x])*(a+b*x-c*Sqrt[1+(a+b*x)^2]*Log[f])/(b*(1-c^2*Log[f]^2))) /;
FreeQ[{a,b,c,f},x] && NonzeroQ[1-c^2*Log[f]^2]

(* ::Code:: *)
Int[ArcSinh[u_],x_Symbol] :=
(Print["Int(24th)@InverseHyperbolicSineFunctions.m"];
  x*ArcSinh[u] -
  Int[Regularize[x*D[u,x]/Sqrt[1+u^2],x],x]) /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialOfLinear[u,x]]

(* ::Code:: *)
Int[E^(n_.*ArcSinh[u_]), x_Symbol] :=
(Print["Int(25th)@InverseHyperbolicSineFunctions.m"];
  Int[(u+Sqrt[1+u^2])^n,x]) /;
IntegerQ[n] && PolynomialQ[u,x]

(* ::Code:: *)
Int[x_^m_.*E^(n_.*ArcSinh[u_]), x_Symbol] :=
(Print["Int(26th)@InverseHyperbolicSineFunctions.m"];
  Int[x^m*(u+Sqrt[1+u^2])^n,x]) /;
RationalQ[m] && IntegerQ[n] && PolynomialQ[u,x]
