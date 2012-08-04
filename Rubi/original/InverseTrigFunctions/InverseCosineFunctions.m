(* ::Package:: *)

(* ::Code:: *)
Int[ArcCos[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@InverseCosineFunctions.m"];
  (a+b*x)*ArcCos[a+b*x]/b - Sqrt[1-(a+b*x)^2]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[ArcCos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(2th)@InverseCosineFunctions.m"];
  (a+b*x)*ArcCos[a+b*x]^n/b -
  n*Sqrt[1-(a+b*x)^2]*ArcCos[a+b*x]^(n-1)/b -
  Dist[n*(n-1),Int[ArcCos[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[1/ArcCos[a_.+b_.*x_],x_Symbol] :=
(Print["Int(3th)@InverseCosineFunctions.m"];
  -SinIntegral[ArcCos[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[1/ArcCos[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(4th)@InverseCosineFunctions.m"];
  Sqrt[1-(a+b*x)^2]/(b*ArcCos[a+b*x]) - CosIntegral[ArcCos[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[1/Sqrt[ArcCos[a_.+b_.*x_]],x_Symbol] :=
(Print["Int(5th)@InverseCosineFunctions.m"];
  -Sqrt[2*Pi]*FresnelS[Sqrt[2/Pi]*Sqrt[ArcCos[a+b*x]]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Sqrt[ArcCos[a_.+b_.*x_]],x_Symbol] :=
(Print["Int(6th)@InverseCosineFunctions.m"];
  (a+b*x)*Sqrt[ArcCos[a+b*x]]/b - Sqrt[Pi/2]*FresnelC[Sqrt[2/Pi]*Sqrt[ArcCos[a+b*x]]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[ArcCos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(7th)@InverseCosineFunctions.m"];
  (a+b*x)*ArcCos[a+b*x]^(n+2)/(b*(n+1)*(n+2)) -
  Sqrt[1-(a+b*x)^2]*ArcCos[a+b*x]^(n+1)/(b*(n+1)) -
  Dist[1/((n+1)*(n+2)),Int[ArcCos[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[ArcCos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(8th)@InverseCosineFunctions.m"];
  ArcCos[a+b*x]^n/(2*b)*
    (Gamma[n+1,I*ArcCos[a+b*x]]/(I*ArcCos[a+b*x])^n + 
     Gamma[n+1,-I*ArcCos[a+b*x]]/(-I*ArcCos[a+b*x])^n)) /;
FreeQ[{a,b,n},x] && (Not[RationalQ[n]] || -1<n<1)

(* ::Code:: *)
Int[x_^m_.*ArcCos[a_.+b_.*x_],x_Symbol] :=
(Print["Int(9th)@InverseCosineFunctions.m"];
  x^(m+1)*ArcCos[a+b*x]/(m+1) +
  Dist[b/(m+1),Int[x^(m+1)/Sqrt[1-a^2-2*a*b*x-b^2*x^2],x]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_/Sqrt[ArcCos[a_.*x_]],x_Symbol] :=
(Print["Int(10th)@InverseCosineFunctions.m"];
  -Sqrt[Pi]/(2*a^2)*FresnelS[2*Sqrt[ArcCos[a*x]]/Sqrt[Pi]]) /;
FreeQ[a,x]

(* ::Code:: *)
Int[x_/ArcCos[a_.*x_]^(3/2),x_Symbol] :=
(Print["Int(11th)@InverseCosineFunctions.m"];
  2*x*Sqrt[1-a^2*x^2]/(a*Sqrt[ArcCos[a*x]]) - 2*Sqrt[Pi]/a^2*FresnelC[2*Sqrt[ArcCos[a*x]]/Sqrt[Pi]]) /;
FreeQ[a,x]

(* ::Code:: *)
Int[x_*ArcCos[a_.*x_]^n_,x_Symbol] :=
(Print["Int(12th)@InverseCosineFunctions.m"];
  -n*x*Sqrt[1-a^2*x^2]*ArcCos[a*x]^(n-1)/(4*a) -
  ArcCos[a*x]^n/(4*a^2) + x^2*ArcCos[a*x]^n/2 -
  Dist[n*(n-1)/4,Int[x*ArcCos[a*x]^(n-2),x]]) /;
FreeQ[a,x] && RationalQ[n] && n>0

(* ::Code:: *)
Int[x_*ArcCos[a_.*x_]^n_,x_Symbol] :=
(Print["Int(13th)@InverseCosineFunctions.m"];
  -x*Sqrt[1-a^2*x^2]*ArcCos[a*x]^(n+1)/(a*(n+1)) -
  ArcCos[a*x]^(n+2)/(a^2*(n+1)*(n+2)) +
  2*x^2*ArcCos[a*x]^(n+2)/((n+1)*(n+2)) -
  Dist[4/((n+1)*(n+2)),Int[x*ArcCos[a*x]^(n+2),x]]) /;
FreeQ[a,x] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[ArcCos[a_.*x_]^n_/x_^3,x_Symbol] :=
(Print["Int(14th)@InverseCosineFunctions.m"];
  a*n*Sqrt[1-a^2*x^2]*ArcCos[a*x]^(n-1)/(2*x) -
  ArcCos[a*x]^n/(2*x^2) +
  Dist[a^2*n*(n-1)/2,Int[ArcCos[a*x]^(n-2)/x,x]]) /;
FreeQ[a,x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[x_^m_*ArcCos[a_.*x_]^n_,x_Symbol] :=
(Print["Int(15th)@InverseCosineFunctions.m"];
  a*n*x^(m+2)*Sqrt[1-a^2*x^2]*ArcCos[a*x]^(n-1)/((m+1)*(m+2)) +
  x^(m+1)*ArcCos[a*x]^n/(m+1) -
  a^2*(m+3)*x^(m+3)*ArcCos[a*x]^n/((m+1)*(m+2)) +
  Dist[a^2*(m+3)^2/((m+1)*(m+2)),Int[x^(m+2)*ArcCos[a*x]^n,x]] +
  Dist[a^2*n*(n-1)/((m+1)*(m+2)),Int[x^(m+2)*ArcCos[a*x]^(n-2),x]]) /;
FreeQ[a,x] && IntegerQ[m] && RationalQ[n] && m<-3 && n>1

(* ::Code:: *)
Int[x_^m_*ArcCos[a_.*x_]^n_,x_Symbol] :=
(Print["Int(16th)@InverseCosineFunctions.m"];
  -x^m*Sqrt[1-a^2*x^2]*ArcCos[a*x]^(n+1)/(a*(n+1)) -
  m*x^(m-1)*ArcCos[a*x]^(n+2)/(a^2*(n+1)*(n+2)) +
  (m+1)*x^(m+1)*ArcCos[a*x]^(n+2)/((n+1)*(n+2)) -
  Dist[(m+1)^2/((n+1)*(n+2)),Int[x^m*ArcCos[a*x]^(n+2),x]] +
  Dist[m*(m-1)/(a^2*(n+1)*(n+2)),Int[x^(m-2)*ArcCos[a*x]^(n+2),x]]) /;
FreeQ[a,x] && IntegerQ[m] && RationalQ[n] && m>1 && n<-1 && n!=-2

(* ::Code:: *)
Int[ArcCos[a_.*x_^p_.]^n_./x_,x_Symbol] :=
(Print["Int(17th)@InverseCosineFunctions.m"];
  -Dist[1/p,Subst[Int[x^n*Tan[x],x],x,ArcCos[a*x^p]]]) /;
FreeQ[{a,p},x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_.*ArcCos[a_.*x_]^n_,x_Symbol] :=
(Print["Int(18th)@InverseCosineFunctions.m"];
  x^(m+1)*ArcCos[a*x]^n/(m+1) -
  Dist[n/(a^(m+1)*(m+1)),Subst[Int[x^(n-1)*Cos[x]^(m+1),x],x,ArcCos[a*x]]]) /;
FreeQ[{a,n},x] && IntegerQ[m] && m!=-1

(* ::Code:: *)
Int[(a_+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(19th)@InverseCosineFunctions.m"];
  -Dist[1/d,Subst[Int[(a+b*x)^n*Sin[x],x],x,ArcCos[c+d*x]]]) /;
FreeQ[{a,b,c,d},x] && Not[IntegerQ[n]]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*ArcCos[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(20th)@InverseCosineFunctions.m"];
  -Dist[1/d^(m+1),Subst[Int[(a+b*x)^n*(Cos[x]-c)^m*Sin[x],x],x,ArcCos[c+d*x]]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && Not[IntegerQ[n]] && m>0

(* ::Code:: *)
Int[x_*ArcCos[a_.+b_.*x_]^n_/Sqrt[u_],x_Symbol] :=
(Print["Int(21th)@InverseCosineFunctions.m"];
  -Sqrt[u]*ArcCos[a+b*x]^n/b^2 -
  Dist[n/b,Int[ArcCos[a+b*x]^(n-1),x]] -
  Dist[a/b,Int[ArcCos[a+b*x]^n/Sqrt[u],x]]) /;
FreeQ[{a,b},x] && ZeroQ[u-1+(a+b*x)^2] && RationalQ[n] && n>1

(* ::Code:: *)
Int[u_.*ArcCos[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
(Print["Int(22th)@InverseCosineFunctions.m"];
  Int[u*ArcSec[a/c+b*x^n/c]^m,x]) /;
FreeQ[{a,b,c,n,m},x]

(* ::Code:: *)
Int[f_^(c_.*ArcCos[a_.+b_.*x_]),x_Symbol] :=
(Print["Int(23th)@InverseCosineFunctions.m"];
  f^(c*ArcCos[a+b*x])*(a+b*x-c*Sqrt[1-(a+b*x)^2]*Log[f])/(b*(1+c^2*Log[f]^2))) /;
FreeQ[{a,b,c,f},x] && NonzeroQ[1+c^2*Log[f]^2]

(* ::Code:: *)
Int[ArcCos[u_],x_Symbol] :=
(Print["Int(24th)@InverseCosineFunctions.m"];
  x*ArcCos[u] +
  Int[Regularize[x*D[u,x]/Sqrt[1-u^2],x],x]) /;
InverseFunctionFreeQ[u,x] && Not[FunctionOfExponentialOfLinear[u,x]]

(* ::Code:: *)
Int[x_^m_.*ArcCos[u_],x_Symbol] :=
(Print["Int(25th)@InverseCosineFunctions.m"];
  x^(m+1)*ArcCos[u]/(m+1) +
  Dist[1/(m+1),Int[Regularize[x^(m+1)*D[u,x]/Sqrt[1-u^2],x],x]]) /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	Not[FunctionOfExponentialOfLinear[u,x]]
