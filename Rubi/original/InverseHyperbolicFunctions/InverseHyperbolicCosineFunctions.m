(* ::Package:: *)

(* ::Code:: *)
Int[ArcCosh[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@InverseHyperbolicCosineFunctions.m"];
  (a+b*x)*ArcCosh[a+b*x]/b - Sqrt[-1+a+b*x]*Sqrt[1+a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[ArcCosh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(2th)@InverseHyperbolicCosineFunctions.m"];
  (a+b*x)*ArcCosh[a+b*x]^n/b -
  n*Sqrt[-1+a+b*x]*Sqrt[1+a+b*x]*ArcCosh[a+b*x]^(n-1)/b +
  Dist[n*(n-1),Int[ArcCosh[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[1/ArcCosh[a_.+b_.*x_],x_Symbol] :=
(Print["Int(3th)@InverseHyperbolicCosineFunctions.m"];
  SinhIntegral[ArcCosh[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[1/ArcCosh[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(4th)@InverseHyperbolicCosineFunctions.m"];
  -Sqrt[-1+a+b*x]*Sqrt[1+a+b*x]/(b*ArcCosh[a+b*x]) + CoshIntegral[ArcCosh[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[1/Sqrt[ArcCosh[a_.+b_.*x_]],x_Symbol] :=
(Print["Int(5th)@InverseHyperbolicCosineFunctions.m"];
  -Sqrt[Pi]*Erf[Sqrt[ArcCosh[a+b*x]]]/(2*b) +
  Sqrt[Pi]*Erfi[Sqrt[ArcCosh[a+b*x]]]/(2*b)) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Sqrt[ArcCosh[a_.+b_.*x_]],x_Symbol] :=
(Print["Int(6th)@InverseHyperbolicCosineFunctions.m"];
  (a+b*x)*Sqrt[ArcCosh[a+b*x]]/b -
  Sqrt[Pi]*Erf[Sqrt[ArcCosh[a+b*x]]]/(4*b) -
  Sqrt[Pi]*Erfi[Sqrt[ArcCosh[a+b*x]]]/(4*b)) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[ArcCosh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(7th)@InverseHyperbolicCosineFunctions.m"];
  -(a+b*x)*ArcCosh[a+b*x]^(n+2)/(b*(n+1)*(n+2)) +
  Sqrt[-1+a+b*x]*Sqrt[1+a+b*x]*ArcCosh[a+b*x]^(n+1)/(b*(n+1)) +
  Dist[1/((n+1)*(n+2)),Int[ArcCosh[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[ArcCosh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(8th)@InverseHyperbolicCosineFunctions.m"];
  ArcCosh[a+b*x]^n*Gamma[n+1,-ArcCosh[a+b*x]]/(2*b*(-ArcCosh[a+b*x])^n) +
  Gamma[n+1,ArcCosh[a+b*x]]/(2*b)) /;
FreeQ[{a,b,n},x] && (Not[RationalQ[n]] || -1<n<1)

(* ::Code:: *)
Int[x_^m_.*ArcCosh[a_.+b_.*x_],x_Symbol] :=
(Print["Int(9th)@InverseHyperbolicCosineFunctions.m"];
  x^(m+1)*ArcCosh[a+b*x]/(m+1) - 
  Dist[b/(m+1),Int[x^(m+1)/(Sqrt[-1+a+b*x]*Sqrt[1+a+b*x]),x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_/Sqrt[ArcCosh[a_.*x_]],x_Symbol] :=
(Print["Int(10th)@InverseHyperbolicCosineFunctions.m"];
  -Sqrt[Pi/2]*Erf[Sqrt[2]*Sqrt[ArcCosh[a*x]]]/(4*a^2) + 
  Sqrt[Pi/2]*Erfi[Sqrt[2]*Sqrt[ArcCosh[a*x]]]/(4*a^2)) /;
FreeQ[a,x]

(* ::Code:: *)
Int[x_/ArcCosh[a_.*x_]^(3/2),x_Symbol] :=
(Print["Int(11th)@InverseHyperbolicCosineFunctions.m"];
  -2*x*Sqrt[-1+a*x]*Sqrt[1+a*x]/(a*Sqrt[ArcCosh[a*x]]) +
  Sqrt[Pi/2]*Erf[Sqrt[2]*Sqrt[ArcCosh[a*x]]]/a^2 +
  Sqrt[Pi/2]*Erfi[Sqrt[2]*Sqrt[ArcCosh[a*x]]]/a^2) /;
FreeQ[a,x]

(* ::Code:: *)
Int[x_*ArcCosh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(12th)@InverseHyperbolicCosineFunctions.m"];
  -n*x*Sqrt[-1+a*x]*Sqrt[1+a*x]*ArcCosh[a*x]^(n-1)/(4*a) -
  ArcCosh[a*x]^n/(4*a^2) + x^2*ArcCosh[a*x]^n/2 +
  Dist[n*(n-1)/4,Int[x*ArcCosh[a*x]^(n-2),x]]) /;
FreeQ[a,x] && RationalQ[n] && n>0

(* ::Code:: *)
Int[x_*ArcCosh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(13th)@InverseHyperbolicCosineFunctions.m"];
  x*Sqrt[-1+a*x]*Sqrt[1+a*x]*ArcCosh[a*x]^(n+1)/(a*(n+1)) +
  ArcCosh[a*x]^(n+2)/(a^2*(n+1)*(n+2)) -
  2*x^2*ArcCosh[a*x]^(n+2)/((n+1)*(n+2)) +
  Dist[4/((n+1)*(n+2)),Int[x*ArcCosh[a*x]^(n+2),x]]) /;
FreeQ[a,x] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[ArcCosh[a_.*x_]^n_/x_^3,x_Symbol] :=
(Print["Int(14th)@InverseHyperbolicCosineFunctions.m"];
  a*n*Sqrt[-1+a*x]*Sqrt[1+a*x]*ArcCosh[a*x]^(n-1)/(2*x) -
  ArcCosh[a*x]^n/(2*x^2) -
  Dist[a^2*n*(n-1)/2,Int[ArcCosh[a*x]^(n-2)/x,x]]) /;
FreeQ[a,x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[x_^m_*ArcCosh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(15th)@InverseHyperbolicCosineFunctions.m"];
  a*n*x^(m+2)*Sqrt[-1+a*x]*Sqrt[1+a*x]*ArcCosh[a*x]^(n-1)/((m+1)*(m+2)) +
  x^(m+1)*ArcCosh[a*x]^n/(m+1) -
  a^2*(m+3)*x^(m+3)*ArcCosh[a*x]^n/((m+1)*(m+2)) +
  Dist[a^2*(m+3)^2/((m+1)*(m+2)),Int[x^(m+2)*ArcCosh[a*x]^n,x]] -
  Dist[a^2*n*(n-1)/((m+1)*(m+2)),Int[x^(m+2)*ArcCosh[a*x]^(n-2),x]]) /;
FreeQ[a,x] && IntegerQ[m] && RationalQ[n] && m<-3 && n>1

(* ::Code:: *)
Int[x_^m_*ArcCosh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(16th)@InverseHyperbolicCosineFunctions.m"];
  x^m*Sqrt[-1+a*x]*Sqrt[1+a*x]*ArcCosh[a*x]^(n+1)/(a*(n+1)) +
  m*x^(m-1)*ArcCosh[a*x]^(n+2)/(a^2*(n+1)*(n+2)) -
  (m+1)*x^(m+1)*ArcCosh[a*x]^(n+2)/((n+1)*(n+2)) +
  Dist[(m+1)^2/((n+1)*(n+2)),Int[x^m*ArcCosh[a*x]^(n+2),x]] -
  Dist[m*(m-1)/(a^2*(n+1)*(n+2)),Int[x^(m-2)*ArcCosh[a*x]^(n+2),x]]) /;
FreeQ[a,x] && IntegerQ[m] && RationalQ[n] && m>1 && n<-1 && n!=-2

(* ::Code:: *)
Int[ArcCosh[a_.*x_^p_.]^n_./x_,x_Symbol] :=
(Print["Int(17th)@InverseHyperbolicCosineFunctions.m"];
  Dist[1/p,Subst[Int[x^n*Tanh[x],x],x,ArcCosh[a*x^p]]]) /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_.*ArcCosh[a_.*x_]^n_,x_Symbol] :=
(Print["Int(18th)@InverseHyperbolicCosineFunctions.m"];
  x^(m+1)*ArcCosh[a*x]^n/(m+1) -
  Dist[n/(a^(m+1)*(m+1)),Subst[Int[x^(n-1)*Cosh[x]^(m+1),x],x,ArcCosh[a*x]]]) /;
FreeQ[{a,n},x] && IntegerQ[m] && m!=-1

(* ::Code:: *)
Int[(a_+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(19th)@InverseHyperbolicCosineFunctions.m"];
  Dist[1/d,Subst[Int[(a+b*x)^n*Sinh[x],x],x,ArcCosh[c+d*x]]]) /;
FreeQ[{a,b,c,d},x] && Not[IntegerQ[n]]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*ArcCosh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(20th)@InverseHyperbolicCosineFunctions.m"];
  Dist[1/d^(m+1),Subst[Int[(a+b*x)^n*(Cosh[x]-c)^m*Sinh[x],x],x,ArcCosh[c+d*x]]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && Not[IntegerQ[n]] && m>0

(* ::Code:: *)
Int[u_.*ArcCosh[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
(Print["Int(21th)@InverseHyperbolicCosineFunctions.m"];
  Int[u*ArcSech[a/c+b*x^n/c]^m,x]) /;
FreeQ[{a,b,c,n,m},x]

(* ::Code:: *)
Int[f_^(c_.*ArcCosh[a_.+b_.*x_]),x_Symbol] :=
(Print["Int(22th)@InverseHyperbolicCosineFunctions.m"];
  (a+b*x-c*Sqrt[(-1+a+b*x)/(1+a+b*x)]*(1+a+b*x)*Log[f])/(b*(1-c^2*Log[f]^2))*
    f^(c*ArcCosh[a+b*x])) /;
FreeQ[{a,b,c,f},x] && NonzeroQ[1-c^2*Log[f]^2]

(* ::Code:: *)
Int[ArcCosh[u_],x_Symbol] :=
(Print["Int(23th)@InverseHyperbolicCosineFunctions.m"];
  x*ArcCosh[u] - 
  Int[Regularize[x*D[u,x]/(Sqrt[-1+u]*Sqrt[1+u]),x],x]) /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialOfLinear[u,x]]

(* ::Code:: *)
Int[E^(n_.*ArcCosh[u_]), x_Symbol] :=
(Print["Int(24th)@InverseHyperbolicCosineFunctions.m"];
  Int[(u+Sqrt[-1+u]*Sqrt[1+u])^n,x]) /;
IntegerQ[n] && PolynomialQ[u,x]

(* ::Code:: *)
Int[x_^m_.*E^(n_.*ArcCosh[u_]), x_Symbol] :=
(Print["Int(25th)@InverseHyperbolicCosineFunctions.m"];
  Int[x^m*(u+Sqrt[-1+u]*Sqrt[1+u])^n,x]) /;
RationalQ[m] && IntegerQ[n] && PolynomialQ[u,x]
