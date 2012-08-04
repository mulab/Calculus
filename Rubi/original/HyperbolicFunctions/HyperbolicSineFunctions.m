(* ::Package:: *)

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(1th)@HyperbolicSineFunctions.m"];
  Dist[(2*a)^n,Int[x^m*Cosh[-Pi*a/(4*b)+c/2+d*x/2]^(2*n),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && IntegerQ[n] && n<0

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(2th)@HyperbolicSineFunctions.m"];
  Dist[(2*a)^(n-1/2)*Sqrt[a+b*Sinh[c+d*x]]/Cosh[-Pi*a/(4*b)+c/2+d*x/2],
    Int[x^m*Cosh[-Pi*a/(4*b)+c/2+d*x/2]^(2*n),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[m] && IntegerQ[n-1/2]

(* ::Code:: *)
Int[x_/(a_+b_.*Sinh[c_.+d_.*x_])^2,x_Symbol] :=
(Print["Int(3th)@HyperbolicSineFunctions.m"];
  Dist[a/(a^2+b^2),Int[x/(a+b*Sinh[c+d*x]),x]] +
  Dist[b/(a^2+b^2),Int[x*(b-a*Sinh[c+d*x])/(a+b*Sinh[c+d*x])^2,x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(4th)@HyperbolicSineFunctions.m"];
  Dist[1/2^n,Int[x^m*(-b+2*a*E^(c+d*x)+b*E^(2*(c+d*x)))^n/E^(n*(c+d*x)),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[m] && m>0 && IntegerQ[n] && n<0

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(5th)@HyperbolicSineFunctions.m"];
  Dist[(2*a)^n,Int[x^m*Cosh[c/2+d*x/2]^(2*n),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && RationalQ[m] && IntegerQ[n] && n<0

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(6th)@HyperbolicSineFunctions.m"];
  Dist[(-2*a)^n,Int[x^m*Sinh[c/2+d*x/2]^(2*n),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b] && RationalQ[m] && IntegerQ[n] && n<0

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(7th)@HyperbolicSineFunctions.m"];
  Dist[(2*a)^(n-1/2)*Sqrt[a+b*Cosh[c+d*x]]/Cosh[c/2+d*x/2],Int[x^m*Cosh[c/2+d*x/2]^(2*n),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && RationalQ[m] && IntegerQ[n-1/2]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(8th)@HyperbolicSineFunctions.m"];
  Dist[(-2*a)^(n-1/2)*Sqrt[a+b*Cosh[c+d*x]]/Sinh[c/2+d*x/2],Int[x^m*Sinh[c/2+d*x/2]^(2*n),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b] && RationalQ[m] && IntegerQ[n-1/2]

(* ::Code:: *)
Int[x_/(a_+b_.*Cosh[c_.+d_.*x_])^2,x_Symbol] :=
(Print["Int(9th)@HyperbolicSineFunctions.m"];
  Dist[a/(a^2-b^2),Int[x/(a+b*Cosh[c+d*x]),x]] -
  Dist[b/(a^2-b^2),Int[x*(b+a*Cosh[c+d*x])/(a+b*Cosh[c+d*x])^2,x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(10th)@HyperbolicSineFunctions.m"];
  Dist[1/2^n,Int[x^m*(b+2*a*E^(c+d*x)+b*E^(2*(c+d*x)))^n/E^(n*(c+d*x)),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[m] && m>0 && IntegerQ[n] && n<0

(* ::Code:: *)
Int[(a_+b_.*Sinh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
(Print["Int(11th)@HyperbolicSineFunctions.m"];
  Dist[1/2^n,Int[(2*a-b+b*Cosh[2*c+2*d*x])^n,x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b] && RationalQ[n] && n!=-1

(* ::Code:: *)
Int[(a_+b_.*Cosh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
(Print["Int(12th)@HyperbolicSineFunctions.m"];
  Dist[1/2^n,Int[(2*a+b+b*Cosh[2*c+2*d*x])^n,x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b] && RationalQ[n] && n!=-1

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Sinh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
(Print["Int(13th)@HyperbolicSineFunctions.m"];
  Dist[1/2^n,Int[x^m*(2*a-b+b*Cosh[2*c+2*d*x])^n,x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b] && IntegersQ[m,n] && (m>0 && n==-1 || m==1 && n==-2)

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*Cosh[c_.+d_.*x_]^2)^n_,x_Symbol] :=
(Print["Int(14th)@HyperbolicSineFunctions.m"];
  Dist[1/2^n,Int[x^m*(2*a+b+b*Cosh[2*c+2*d*x])^n,x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a+b] && IntegersQ[m,n] && (m>0 && n==-1 || m==1 && n==-2)

(* ::Code:: *)
(* Int[Sinh[b_.*x_^2],x_Symbol] :=
(Print["Int(15th)@HyperbolicSineFunctions.m"];
  -I*Sqrt[Pi/2]*FresnelS[Rt[I*b,2]*x/Sqrt[Pi/2]]/Rt[I*b,2]) /;
FreeQ[b,x] *)

(* ::Code:: *)
(* Int[Cosh[b_.*x_^2],x_Symbol] :=
(Print["Int(16th)@HyperbolicSineFunctions.m"];
  Sqrt[Pi/2]*FresnelC[Rt[I*b,2]*x/Sqrt[Pi/2]]/Rt[I*b,2]) /;
FreeQ[b,x] *)

(* ::Code:: *)
Int[Sinh[a_.+b_.*x_^n_],x_Symbol] :=
(Print["Int(17th)@HyperbolicSineFunctions.m"];
  Dist[1/2,Int[E^(a+b*x^n),x]] - 
  Dist[1/2,Int[E^(-a-b*x^n),x]]) /;
FreeQ[{a,b,n},x] && Not[FractionOrNegativeQ[n]]

(* ::Code:: *)
Int[Cosh[a_.+b_.*x_^n_],x_Symbol] :=
(Print["Int(18th)@HyperbolicSineFunctions.m"];
  Dist[1/2,Int[E^(-a-b*x^n),x]] + 
  Dist[1/2,Int[E^(a+b*x^n),x]]) /;
FreeQ[{a,b,n},x] && Not[FractionOrNegativeQ[n]]

(* ::Code:: *)
Int[Sinh[a_.+b_.*x_^n_],x_Symbol] :=
(Print["Int(19th)@HyperbolicSineFunctions.m"];
  x*Sinh[a+b*x^n] - 
  Dist[b*n,Int[x^n*Cosh[a+b*x^n],x]]) /;
FreeQ[{a,b},x] && IntegerQ[n] && n<0

(* ::Code:: *)
Int[Cosh[a_.+b_.*x_^n_],x_Symbol] :=
(Print["Int(20th)@HyperbolicSineFunctions.m"];
  x*Cosh[a+b*x^n] - 
  Dist[b*n,Int[x^n*Sinh[a+b*x^n],x]]) /;
FreeQ[{a,b},x] && IntegerQ[n] && n<0

(* ::Code:: *)
Int[Sinh[b_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(21th)@HyperbolicSineFunctions.m"];
  SinhIntegral[b*x^n]/n) /;
FreeQ[{b,n},x]

(* ::Code:: *)
Int[Cosh[b_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(22th)@HyperbolicSineFunctions.m"];
  CoshIntegral[b*x^n]/n) /;
FreeQ[{b,n},x]

(* ::Code:: *)
Int[Sinh[a_+b_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(23th)@HyperbolicSineFunctions.m"];
  Dist[Sinh[a],Int[Cosh[b*x^n]/x,x]] + 
  Dist[Cosh[a],Int[Sinh[b*x^n]/x,x]]) /;
FreeQ[{a,b,n},x]

(* ::Code:: *)
Int[Cosh[a_+b_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(24th)@HyperbolicSineFunctions.m"];
  Dist[Cosh[a],Int[Cosh[b*x^n]/x,x]] + 
  Dist[Sinh[a],Int[Sinh[b*x^n]/x,x]]) /;
FreeQ[{a,b,n},x]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(25th)@HyperbolicSineFunctions.m"];
  x^(m-n+1)*Cosh[a+b*x^n]/(b*n) -
  Dist[(m-n+1)/(b*n),Int[x^(m-n)*Cosh[a+b*x^n],x]]) /;
FreeQ[{a,b},x] && IntegerQ[n] && RationalQ[m] && 0<n<=m

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(26th)@HyperbolicSineFunctions.m"];
  x^(m-n+1)*Sinh[a+b*x^n]/(b*n) -
  Dist[(m-n+1)/(b*n),Int[x^(m-n)*Sinh[a+b*x^n],x]]) /;
FreeQ[{a,b},x] && IntegerQ[n] && RationalQ[m] && 0<n<=m

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(27th)@HyperbolicSineFunctions.m"];
  x^(m+1)*Sinh[a+b*x^n]/(m+1) -
  Dist[b*n/(m+1),Int[x^(m+n)*Cosh[a+b*x^n],x]]) /;
FreeQ[{a,b,m,n},x] && (ZeroQ[m+n+1] || IntegerQ[n] && RationalQ[m] && (n>0 && m<-1 || 0<-n<m+1))

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(28th)@HyperbolicSineFunctions.m"];
  x^(m+1)*Cosh[a+b*x^n]/(m+1) -
  Dist[b*n/(m+1),Int[x^(m+n)*Sinh[a+b*x^n],x]]) /;
FreeQ[{a,b,m,n},x] && (ZeroQ[m+n+1] || IntegerQ[n] && RationalQ[m] && (n>0 && m<-1 || 0<-n<m+1))

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(29th)@HyperbolicSineFunctions.m"];
  Dist[1/2,Int[x^m*E^(a+b*x^n),x]] - 
  Dist[1/2,Int[x^m*E^(-a-b*x^n),x]]) /;
FreeQ[{a,b,m,n},x] && NonzeroQ[m+1] && NonzeroQ[m-n+1] &&
Not[FractionQ[m] || FractionOrNegativeQ[n]]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(30th)@HyperbolicSineFunctions.m"];
  Dist[1/2,Int[x^m*E^(-a-b*x^n),x]] + 
  Dist[1/2,Int[x^m*E^(a+b*x^n),x]]) /;
FreeQ[{a,b,m,n},x] && NonzeroQ[m+1] && NonzeroQ[m-n+1] && 
Not[FractionQ[m] || FractionOrNegativeQ[n]]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(31th)@HyperbolicSineFunctions.m"];
  -Sinh[a+b*x^n]^p/((n-1)*x^(n-1)) +
  Dist[b*n*p/(n-1),Int[Sinh[a+b*x^n]^(p-1)*Cosh[a+b*x^n],x]]) /;
FreeQ[{a,b},x] && IntegersQ[n,p] && ZeroQ[m+n] && p>1 && NonzeroQ[n-1]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(32th)@HyperbolicSineFunctions.m"];
  -Cosh[a+b*x^n]^p/((n-1)*x^(n-1)) +
  Dist[b*n*p/(n-1),Int[Cosh[a+b*x^n]^(p-1)*Sinh[a+b*x^n],x]]) /;
FreeQ[{a,b},x] && IntegersQ[n,p] && ZeroQ[m+n] && p>1 && NonzeroQ[n-1]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(33th)@HyperbolicSineFunctions.m"];
  -n*Sinh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^n*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/(b*n*p) -
  Dist[(p-1)/p,Int[x^m*Sinh[a+b*x^n]^(p-2),x]]) /;
FreeQ[{a,b,m,n},x] && RationalQ[p] && p>1 && ZeroQ[m-2*n+1]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(34th)@HyperbolicSineFunctions.m"];
  -n*Cosh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^n*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/(b*n*p) +
  Dist[(p-1)/p,Int[x^m*Cosh[a+b*x^n]^(p-2),x]]) /;
FreeQ[{a,b,m,n},x] && RationalQ[p] && p>1 && ZeroQ[m-2*n+1]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(35th)@HyperbolicSineFunctions.m"];
  -(m-n+1)*x^(m-2*n+1)*Sinh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^(m-n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/(b*n*p) -
  Dist[(p-1)/p,Int[x^m*Sinh[a+b*x^n]^(p-2),x]] +
  Dist[(m-n+1)*(m-2*n+1)/(b^2*n^2*p^2),Int[x^(m-2*n)*Sinh[a+b*x^n]^p,x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<m+1

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(36th)@HyperbolicSineFunctions.m"];
  -(m-n+1)*x^(m-2*n+1)*Cosh[a+b*x^n]^p/(b^2*n^2*p^2) +
  x^(m-n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/(b*n*p) +
  Dist[(p-1)/p,Int[x^m*Cosh[a+b*x^n]^(p-2),x]] +
  Dist[(m-n+1)*(m-2*n+1)/(b^2*n^2*p^2),Int[x^(m-2*n)*Cosh[a+b*x^n]^p,x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<m+1

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(37th)@HyperbolicSineFunctions.m"];
  x^n*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) - 
  n*Sinh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) - 
  Dist[(p+2)/(p+1),Int[x^m*Sinh[a+b*x^n]^(p+2),x]]) /;
FreeQ[{a,b,m,n},x] && RationalQ[p] && p<-1 && p!=-2 && ZeroQ[m-2*n+1]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(38th)@HyperbolicSineFunctions.m"];
  -x^n*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) + 
  n*Cosh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) + 
  Dist[(p+2)/(p+1),Int[x^m*Cosh[a+b*x^n]^(p+2),x]]) /;
FreeQ[{a,b,m,n},x] && RationalQ[p] && p<-1 && p!=-2 && ZeroQ[m-2*n+1]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(39th)@HyperbolicSineFunctions.m"];
  x^(m-n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  (m-n+1)*x^(m-2*n+1)*Sinh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) -
  Dist[(p+2)/(p+1),Int[x^m*Sinh[a+b*x^n]^(p+2),x]] +
  Dist[(m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2)),Int[x^(m-2*n)*Sinh[a+b*x^n]^(p+2),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p<-1 && p!=-2 && 0<2*n<m+1

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(40th)@HyperbolicSineFunctions.m"];
  -x^(m-n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p+1)/(b*n*(p+1)) +
  (m-n+1)*x^(m-2*n+1)*Cosh[a+b*x^n]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  Dist[(p+2)/(p+1),Int[x^m*Cosh[a+b*x^n]^(p+2),x]] -
  Dist[(m-n+1)*(m-2*n+1)/(b^2*n^2*(p+1)*(p+2)),Int[x^(m-2*n)*Cosh[a+b*x^n]^(p+2),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p<-1 && p!=-2 && 0<2*n<m+1

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(41th)@HyperbolicSineFunctions.m"];
  x^(m+1)*Sinh[a+b*x^n]^p/(m+1) - 
  b*n*p*x^(m+n+1)*Cosh[a+b*x^n]*Sinh[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) + 
  Dist[b^2*n^2*p^2/((m+1)*(m+n+1)),Int[x^(m+2*n)*Sinh[a+b*x^n]^p,x]] + 
  Dist[b^2*n^2*p*(p-1)/((m+1)*(m+n+1)),Int[x^(m+2*n)*Sinh[a+b*x^n]^(p-2),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<-m+1 && NonzeroQ[m+n+1]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(42th)@HyperbolicSineFunctions.m"];
  x^(m+1)*Cosh[a+b*x^n]^p/(m+1) - 
  b*n*p*x^(m+n+1)*Sinh[a+b*x^n]*Cosh[a+b*x^n]^(p-1)/((m+1)*(m+n+1)) + 
  Dist[b^2*n^2*p^2/((m+1)*(m+n+1)),Int[x^(m+2*n)*Cosh[a+b*x^n]^p,x]] - 
  Dist[b^2*n^2*p*(p-1)/((m+1)*(m+n+1)),Int[x^(m+2*n)*Cosh[a+b*x^n]^(p-2),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && RationalQ[p] && p>1 && 0<2*n<-m+1 && NonzeroQ[m+n+1]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
(Print["Int(43th)@HyperbolicSineFunctions.m"];
  Dist[1/d,Subst[Int[(-c/d+x/d)^m*Sinh[a+b*x^n]^p,x],x,c+d*x]]) /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m] && m>0 && RationalQ[p]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*(c_+d_.*x_)^n_]^p_.,x_Symbol] :=
(Print["Int(44th)@HyperbolicSineFunctions.m"];
  Dist[1/d,Subst[Int[(-c/d+x/d)^m*Cosh[a+b*x^n]^p,x],x,c+d*x]]) /;
FreeQ[{a,b,c,d,n},x] && IntegerQ[m] && m>0 && RationalQ[p]

(* ::Code:: *)
Int[Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(45th)@HyperbolicSineFunctions.m"];
  Int[Sinh[(b+2*c*x)^2/(4*c)],x]) /;
FreeQ[{a,b,c},x] && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(46th)@HyperbolicSineFunctions.m"];
  Int[Cosh[(b+2*c*x)^2/(4*c)],x]) /;
FreeQ[{a,b,c},x] && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(47th)@HyperbolicSineFunctions.m"];
  Dist[1/2,Int[E^(a+b*x+c*x^2),x]] - 
  Dist[1/2,Int[E^(-a-b*x-c*x^2),x]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(48th)@HyperbolicSineFunctions.m"];
  Dist[1/2,Int[E^(a+b*x+c*x^2),x]] + 
  Dist[1/2,Int[E^(-a-b*x-c*x^2),x]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(d_.+e_.*x_)*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(49th)@HyperbolicSineFunctions.m"];
  e*Cosh[a+b*x+c*x^2]/(2*c)) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(50th)@HyperbolicSineFunctions.m"];
  e*Sinh[a+b*x+c*x^2]/(2*c)) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(51th)@HyperbolicSineFunctions.m"];
  e*Cosh[a+b*x+c*x^2]/(2*c) -
  Dist[(b*e-2*c*d)/(2*c),Int[Sinh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(52th)@HyperbolicSineFunctions.m"];
  e*Sinh[a+b*x+c*x^2]/(2*c) - 
  Dist[(b*e-2*c*d)/(2*c),Int[Cosh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(53th)@HyperbolicSineFunctions.m"];
  e*(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2]/(2*c) -
  Dist[e^2*(m-1)/(2*c),Int[(d+e*x)^(m-2)*Cosh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && ZeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(54th)@HyperbolicSineFunctions.m"];
  e*(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2]/(2*c) - 
  Dist[e^2*(m-1)/(2*c),Int[(d+e*x)^(m-2)*Sinh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && ZeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(55th)@HyperbolicSineFunctions.m"];
  e*(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2]/(2*c) -
  Dist[(b*e-2*c*d)/(2*c),Int[(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2],x]] -
  Dist[e^2*(m-1)/(2*c),Int[(d+e*x)^(m-2)*Cosh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && NonzeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(56th)@HyperbolicSineFunctions.m"];
  e*(d+e*x)^(m-1)*Sinh[a+b*x+c*x^2]/(2*c) - 
  Dist[(b*e-2*c*d)/(2*c),Int[(d+e*x)^(m-1)*Cosh[a+b*x+c*x^2],x]] - 
  Dist[e^2*(m-1)/(2*c),Int[(d+e*x)^(m-2)*Sinh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m>1 && NonzeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(57th)@HyperbolicSineFunctions.m"];
  (d+e*x)^(m+1)*Sinh[a+b*x+c*x^2]/(e*(m+1)) -
  Dist[2*c/(e^2*(m+1)),Int[(d+e*x)^(m+2)*Cosh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && ZeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(58th)@HyperbolicSineFunctions.m"];
  (d+e*x)^(m+1)*Cosh[a+b*x+c*x^2]/(e*(m+1)) - 
  Dist[2*c/(e^2*(m+1)),Int[(d+e*x)^(m+2)*Sinh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && ZeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*Sinh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(59th)@HyperbolicSineFunctions.m"];
  (d+e*x)^(m+1)*Sinh[a+b*x+c*x^2]/(e*(m+1)) -
  Dist[(b*e-2*c*d)/(e^2*(m+1)),Int[(d+e*x)^(m+1)*Cosh[a+b*x+c*x^2],x]] -
  Dist[2*c/(e^2*(m+1)),Int[(d+e*x)^(m+2)*Cosh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && NonzeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*Cosh[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(60th)@HyperbolicSineFunctions.m"];
  (d+e*x)^(m+1)*Cosh[a+b*x+c*x^2]/(e*(m+1)) - 
  Dist[(b*e-2*c*d)/(e^2*(m+1)),Int[(d+e*x)^(m+1)*Sinh[a+b*x+c*x^2],x]] -
  Dist[2*c/(e^2*(m+1)),Int[(d+e*x)^(m+2)*Sinh[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c,d,e},x] && RationalQ[m] && m<-1 && NonzeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[Sinh[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
(Print["Int(61th)@HyperbolicSineFunctions.m"];
  Int[((c*x^n)^b/2 - 1/(2*(c*x^n)^b))^p,x]) /;
FreeQ[c,x] && RationalQ[{b,n,p}]

(* ::Code:: *)
Int[Cosh[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
(Print["Int(62th)@HyperbolicSineFunctions.m"];
  Int[((c*x^n)^b/2 + 1/(2*(c*x^n)^b))^p,x]) /;
FreeQ[c,x] && RationalQ[{b,n,p}]

(* ::Code:: *)
Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
(Print["Int(63th)@HyperbolicSineFunctions.m"];
  x*Sinh[a+b*Log[c*x^n]]/(1-b^2*n^2) -
  b*n*x*Cosh[a+b*Log[c*x^n]]/(1-b^2*n^2)) /;
FreeQ[{a,b,c,n},x] && NonzeroQ[1-b^2*n^2]

(* ::Code:: *)
Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
(Print["Int(64th)@HyperbolicSineFunctions.m"];
  x*Cosh[a+b*Log[c*x^n]]/(1-b^2*n^2) -
  b*n*x*Sinh[a+b*Log[c*x^n]]/(1-b^2*n^2)) /;
FreeQ[{a,b,c,n},x] && NonzeroQ[1-b^2*n^2]

(* ::Code:: *)
Int[Sqrt[Sinh[a_.+b_.*Log[c_.*x_^n_.]]],x_Symbol] :=
(Print["Int(65th)@HyperbolicSineFunctions.m"];
  x*Sqrt[Sinh[a+b*Log[c*x^n]]]/Sqrt[-1+E^(2*a)*(c*x^n)^(4/n)]*
    Int[Sqrt[-1+E^(2*a)*(c*x^n)^(4/n)]/x,x]) /;
FreeQ[{a,b,c,n},x] && ZeroQ[b*n-2]

(* ::Code:: *)
Int[Sqrt[Cosh[a_.+b_.*Log[c_.*x_^n_.]]],x_Symbol] :=
(Print["Int(66th)@HyperbolicSineFunctions.m"];
  x*Sqrt[Cosh[a+b*Log[c*x^n]]]/Sqrt[1+E^(2*a)*(c*x^n)^(4/n)]*
    Int[Sqrt[1+E^(2*a)*(c*x^n)^(4/n)]/x,x]) /;
FreeQ[{a,b,c,n},x] && ZeroQ[b*n-2]

(* ::Code:: *)
Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(67th)@HyperbolicSineFunctions.m"];
  x*Sinh[a+b*Log[c*x^n]]^p/(1-b^2*n^2*p^2) -
  b*n*p*x*Cosh[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p-1)/(1-b^2*n^2*p^2) +
  Dist[b^2*n^2*p*(p-1)/(1-b^2*n^2*p^2),Int[Sinh[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && NonzeroQ[1-b^2*n^2*p^2]

(* ::Code:: *)
Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(68th)@HyperbolicSineFunctions.m"];
  x*Cosh[a+b*Log[c*x^n]]^p/(1-b^2*n^2*p^2) -
  b*n*p*x*Sinh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p-1)/(1-b^2*n^2*p^2) -
  Dist[b^2*n^2*p*(p-1)/(1-b^2*n^2*p^2),Int[Cosh[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && NonzeroQ[1-b^2*n^2*p^2]

(* ::Code:: *)
Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(69th)@HyperbolicSineFunctions.m"];
  x*Coth[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  x*Sinh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2))) /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[p+1] && NonzeroQ[p+2] && ZeroQ[1-b^2*n^2*(p+2)^2]

(* ::Code:: *)
Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(70th)@HyperbolicSineFunctions.m"];
  -x*Tanh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) +
  x*Cosh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2))) /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[p+1] && NonzeroQ[p+2] && ZeroQ[1-b^2*n^2*(p+2)^2]

(* ::Code:: *)
Int[Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(71th)@HyperbolicSineFunctions.m"];
  x*Coth[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  x*Sinh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  Dist[(1-b^2*n^2*(p+2)^2)/(b^2*n^2*(p+1)*(p+2)),Int[Sinh[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[1-b^2*n^2*(p+2)^2]

(* ::Code:: *)
Int[Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(72th)@HyperbolicSineFunctions.m"];
  -x*Tanh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) +
  x*Cosh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) -
  Dist[(1-b^2*n^2*(p+2)^2)/(b^2*n^2*(p+1)*(p+2)),Int[Cosh[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[1-b^2*n^2*(p+2)^2]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
(Print["Int(73th)@HyperbolicSineFunctions.m"];
  (m+1)*x^(m+1)*Sinh[a+b*Log[c*x^n]]/((m+1)^2-b^2*n^2) -
  b*n*x^(m+1)*Cosh[a+b*Log[c*x^n]]/((m+1)^2-b^2*n^2)) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[(m+1)^2-b^2*n^2] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
(Print["Int(74th)@HyperbolicSineFunctions.m"];
  (m+1)*x^(m+1)*Cosh[a+b*Log[c*x^n]]/((m+1)^2-b^2*n^2) -
  b*n*x^(m+1)*Sinh[a+b*Log[c*x^n]]/((m+1)^2-b^2*n^2)) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[(m+1)^2-b^2*n^2] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(75th)@HyperbolicSineFunctions.m"];
  (m+1)*x^(m+1)*Sinh[a+b*Log[c*x^n]]^p/((m+1)^2-b^2*n^2*p^2) -
  b*n*p*x^(m+1)*Cosh[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p-1)/((m+1)^2-b^2*n^2*p^2) +
  Dist[b^2*n^2*p*(p-1)/((m+1)^2-b^2*n^2*p^2),Int[x^m*Sinh[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[(m+1)^2-b^2*n^2*p^2] && RationalQ[p] && p>1 && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(76th)@HyperbolicSineFunctions.m"];
  (m+1)*x^(m+1)*Cosh[a+b*Log[c*x^n]]^p/((m+1)^2-b^2*n^2*p^2) -
  b*n*p*x^(m+1)*Cosh[a+b*Log[c*x^n]]^(p-1)*Sinh[a+b*Log[c*x^n]]/((m+1)^2-b^2*n^2*p^2) -
  Dist[b^2*n^2*p*(p-1)/((m+1)^2-b^2*n^2*p^2),Int[x^m*Cosh[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[(m+1)^2-b^2*n^2*p^2] && RationalQ[p] && p>1 && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(77th)@HyperbolicSineFunctions.m"];
  x^(m+1)*Coth[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  (m+1)*x^(m+1)*Sinh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2))) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[(m+1)^2-b^2*n^2*(p+2)^2] && NonzeroQ[p+1] && NonzeroQ[p+2]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(78th)@HyperbolicSineFunctions.m"];
  -x^(m+1)*Tanh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) +
  (m+1)*x^(m+1)*Cosh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2))) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[(m+1)^2-b^2*n^2*(p+2)^2] && NonzeroQ[p+1] && NonzeroQ[p+2]

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(79th)@HyperbolicSineFunctions.m"];
  x^(m+1)*Coth[a+b*Log[c*x^n]]*Sinh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) -
  (m+1)*x^(m+1)*Sinh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) +
  Dist[((m+1)^2-b^2*n^2*(p+2)^2)/(b^2*n^2*(p+1)*(p+2)),Int[x^m*Sinh[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[(m+1)^2-b^2*n^2*(p+2)^2] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(80th)@HyperbolicSineFunctions.m"];
  -x^(m+1)*Tanh[a+b*Log[c*x^n]]*Cosh[a+b*Log[c*x^n]]^(p+2)/(b*n*(p+1)) +
  (m+1)*x^(m+1)*Cosh[a+b*Log[c*x^n]]^(p+2)/(b^2*n^2*(p+1)*(p+2)) -
  Dist[((m+1)^2-b^2*n^2*(p+2)^2)/(b^2*n^2*(p+1)*(p+2)),Int[x^m*Cosh[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[(m+1)^2-b^2*n^2*(p+2)^2] && RationalQ[p] && p<-1 && p!=-2 && NonzeroQ[m+1]

(* ::Code:: *)
Int[Sinh[a_.*x_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
(Print["Int(81th)@HyperbolicSineFunctions.m"];
  Cosh[a*x*Log[b*x]^p]/a -
  Dist[p,Int[Sinh[a*x*Log[b*x]^p]*Log[b*x]^(p-1),x]]) /;
FreeQ[{a,b},x] && RationalQ[p] && p>0

(* ::Code:: *)
Int[Cosh[a_.*x_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
(Print["Int(82th)@HyperbolicSineFunctions.m"];
  Sinh[a*x*Log[b*x]^p]/a -
  Dist[p,Int[Cosh[a*x*Log[b*x]^p]*Log[b*x]^(p-1),x]]) /;
FreeQ[{a,b},x] && RationalQ[p] && p>0

(* ::Code:: *)
Int[Sinh[a_.*x_^n_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
(Print["Int(83th)@HyperbolicSineFunctions.m"];
  Cosh[a*x^n*Log[b*x]^p]/(a*n*x^(n-1)) -
  Dist[p/n,Int[Sinh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x]] +
  Dist[(n-1)/(a*n),Int[Cosh[a*x^n*Log[b*x]^p]/x^n,x]]) /;
FreeQ[{a,b},x] && RationalQ[{n,p}] && p>0

(* ::Code:: *)
Int[Cosh[a_.*x_^n_*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
(Print["Int(84th)@HyperbolicSineFunctions.m"];
  Sinh[a*x^n*Log[b*x]^p]/(a*n*x^(n-1)) -
  Dist[p/n,Int[Cosh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x]] +
  Dist[(n-1)/(a*n),Int[Sinh[a*x^n*Log[b*x]^p]/x^n,x]]) /;
FreeQ[{a,b},x] && RationalQ[{n,p}] && p>0

(* ::Code:: *)
Int[x_^m_.*Sinh[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
(Print["Int(85th)@HyperbolicSineFunctions.m"];
  Cosh[a*x^n*Log[b*x]^p]/(a*n) -
  Dist[p/n,Int[x^m*Sinh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n,p}] && p>0 && ZeroQ[m-n+1]

(* ::Code:: *)
Int[x_^m_.*Cosh[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
(Print["Int(86th)@HyperbolicSineFunctions.m"];
  Sinh[a*x^n*Log[b*x]^p]/(a*n) -
  Dist[p/n,Int[x^m*Cosh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n,p}] && p>0 && ZeroQ[m-n+1]

(* ::Code:: *)
Int[x_^m_*Sinh[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
(Print["Int(87th)@HyperbolicSineFunctions.m"];
  x^(m-n+1)*Cosh[a*x^n*Log[b*x]^p]/(a*n) -
  Dist[p/n,Int[x^m*Sinh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x]] -
  Dist[(m-n+1)/(a*n),Int[x^(m-n)*Cosh[a*x^n*Log[b*x]^p],x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n,p}] && p>0 && NonzeroQ[m-n+1]

(* ::Code:: *)
Int[x_^m_*Cosh[a_.*x_^n_.*Log[b_.*x_]^p_.]*Log[b_.*x_]^p_.,x_Symbol] :=
(Print["Int(88th)@HyperbolicSineFunctions.m"];
  x^(m-n+1)*Sinh[a*x^n*Log[b*x]^p]/(a*n) -
  Dist[p/n,Int[x^m*Cosh[a*x^n*Log[b*x]^p]*Log[b*x]^(p-1),x]] -
  Dist[(m-n+1)/(a*n),Int[x^(m-n)*Sinh[a*x^n*Log[b*x]^p],x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n,p}] && p>0 && NonzeroQ[m-n+1]

(* ::Code:: *)
Int[Sinh[c_.+d_.*x_]^2*Sinh[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(89th)@HyperbolicSineFunctions.m"];
  -Dist[1/2,Int[Sinh[a+b*x]^n,x]] + 
  Dist[1/2,Int[Cosh[a+b*x]*Sinh[a+b*x]^n,x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-a/2] && ZeroQ[d-b/2] && Not[OddQ[n]]

(* ::Code:: *)
Int[Cosh[c_.+d_.*x_]^2*Sinh[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(90th)@HyperbolicSineFunctions.m"];
  Dist[1/2,Int[Sinh[a+b*x]^n,x]] + 
  Dist[1/2,Int[Cosh[a+b*x]*Sinh[a+b*x]^n,x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-a/2] && ZeroQ[d-b/2] && Not[OddQ[n]]

(* ::Code:: *)
Int[u_*Sinh[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(91th)@HyperbolicSineFunctions.m"];
  Dist[2^n,Int[u*Cosh[a/2+b*x/2]^n*Sinh[a/2+b*x/2]^n,x]]) /;
FreeQ[{a,b},x] && IntegerQ[n] && ZeroQ[a/2+b*x/2-FunctionOfHyperbolic[u,x]]

(* ::Code:: *)
Int[u_*Sinh[v_]^2,x_Symbol] :=
(Print["Int(92th)@HyperbolicSineFunctions.m"];
  Dist[-1/2,Int[u,x]] + 
  Dist[1/2,Int[u*Cosh[2*v],x]]) /;
FunctionOfHyperbolicQ[u,2*v,x]

(* ::Code:: *)
Int[u_*Cosh[v_]^2,x_Symbol] :=
(Print["Int(93th)@HyperbolicSineFunctions.m"];
  Dist[1/2,Int[u,x]] + 
  Dist[1/2,Int[u*Cosh[2*v],x]]) /;
FunctionOfHyperbolicQ[u,2*v,x]

