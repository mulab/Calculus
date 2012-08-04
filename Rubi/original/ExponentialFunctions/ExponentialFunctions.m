(* ::Package:: *)

(* ::Code:: *)
Int[E^(a_.+b_.*x_),x_Symbol] :=
(Print["Int(1th)@ExponentialFunctions.m"];
  E^(a+b*x)/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[f_^(a_.+b_.*x_),x_Symbol] :=
(Print["Int(2th)@ExponentialFunctions.m"];
  f^(a+b*x)/(b*Log[f])) /;
FreeQ[{a,b,f},x]

(* ::Code:: *)
Int[E^(a_.+b_.*x_^2),x_Symbol] :=
(Print["Int(3th)@ExponentialFunctions.m"];
  E^a*Sqrt[Pi]*Erfi[x*Rt[b,2]]/(2*Rt[b,2])) /;
FreeQ[{a,b},x] && PosQ[b]

(* ::Code:: *)
Int[f_^(a_.+b_.*x_^2),x_Symbol] :=
(Print["Int(4th)@ExponentialFunctions.m"];
  f^a*Sqrt[Pi]*Erfi[x*Rt[b*Log[f],2]]/(2*Rt[b*Log[f],2])) /;
FreeQ[{a,b,f},x] && PosQ[b*Log[f]]

(* ::Code:: *)
Int[E^(a_.+b_.*x_^2),x_Symbol] :=
(Print["Int(5th)@ExponentialFunctions.m"];
  E^a*Sqrt[Pi]*Erf[x*Rt[-b,2]]/(2*Rt[-b,2])) /;
FreeQ[{a,b},x] && NegQ[b]

(* ::Code:: *)
Int[f_^(a_.+b_.*x_^2),x_Symbol] :=
(Print["Int(6th)@ExponentialFunctions.m"];
  f^a*Sqrt[Pi]*Erf[x*Rt[-b*Log[f],2]]/(2*Rt[-b*Log[f],2])) /;
FreeQ[{a,b,f},x] && NegQ[b*Log[f]]

(* ::Code:: *)
Int[E^(a_.+b_.*x_^n_),x_Symbol] :=
(Print["Int(7th)@ExponentialFunctions.m"];
  -E^a*x*Gamma[1/n,-b*x^n]/(n*(-b*x^n)^(1/n))) /;
FreeQ[{a,b,n},x] && Not[FractionOrNegativeQ[n]]

(* ::Code:: *)
Int[f_^(a_.+b_.*x_^n_),x_Symbol] :=
(Print["Int(8th)@ExponentialFunctions.m"];
  -f^a*x*Gamma[1/n,-b*x^n*Log[f]]/(n*(-b*x^n*Log[f])^(1/n))) /;
FreeQ[{a,b,f,n},x] && Not[FractionOrNegativeQ[n]]

(* ::Code:: *)
Int[E^(a_.+b_.*x_^n_.),x_Symbol] :=
(Print["Int(9th)@ExponentialFunctions.m"];
  x*E^(a+b*x^n) - 
  Dist[b*n,Int[x^n*E^(a+b*x^n),x]]) /;
FreeQ[{a,b},x] && IntegerQ[n] && n<0

(* ::Code:: *)
Int[f_^(a_.+b_.*x_^n_.),x_Symbol] :=
(Print["Int(10th)@ExponentialFunctions.m"];
  x*f^(a+b*x^n) - 
  Dist[b*n*Log[f],Int[x^n*f^(a+b*x^n),x]]) /;
FreeQ[{a,b,f},x] && IntegerQ[n] && n<0

(* ::Code:: *)
Int[f_^(a_.+b_.*x_^n_.)/x_,x_Symbol] :=
(Print["Int(11th)@ExponentialFunctions.m"];
  f^a*ExpIntegralEi[b*x^n*Log[f]]/n) /;
FreeQ[{a,b,f,n},x]

(* ::Code:: *)
Int[x_^m_.*f_^(a_.+b_.*x_^n_.),x_Symbol] :=
(Print["Int(12th)@ExponentialFunctions.m"];
  x^(m-n+1)*f^(a+b*x^n)/(b*n*Log[f]) -
  Dist[(m-n+1)/(b*n*Log[f]),Int[x^(m-n)*f^(a+b*x^n),x]]) /;
FreeQ[{a,b,f},x] && IntegerQ[n] && RationalQ[m] && 0<n<=m

(* ::Code:: *)
Int[x_^m_.*f_^(a_.+b_.*x_^n_.),x_Symbol] :=
(Print["Int(13th)@ExponentialFunctions.m"];
  x^(m+1)*f^(a+b*x^n)/(m+1) -
  Dist[b*n*Log[f]/(m+1),Int[x^(m+n)*f^(a+b*x^n),x]]) /;
FreeQ[{a,b,f},x] && IntegerQ[n] && RationalQ[m] && (n>0 && m<-1 || 0<-n<=m+1)

(* ::Code:: *)
Int[x_^m_.*f_^(a_.+b_.*x_^n_.),x_Symbol] :=
(Print["Int(14th)@ExponentialFunctions.m"];
  -f^a*x^(m+1)*Gamma[(m+1)/n,-b*x^n*Log[f]]/(n*(-b*x^n*Log[f])^((m+1)/n))) /;
FreeQ[{a,b,f,m,n},x] &&
  NonzeroQ[m+1] &&
  NonzeroQ[m-n+1] &&
  Not[m===-1/2 && ZeroQ[n-1]] &&
  Not[IntegersQ[m,n] && n>0 && (m<-1 || m>=n)] &&
  Not[RationalQ[{m,n}] && (FractionQ[m] || FractionOrNegativeQ[n])]

(* ::Code:: *)
Int[f_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(15th)@ExponentialFunctions.m"];
  f^(a-b^2/(4*c))*Int[f^((b+2*c*x)^2/(4*c)),x]) /;
FreeQ[{a,b,c,f},x]

(* ::Code:: *)
Int[(d_.+e_.*x_)*f_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(16th)@ExponentialFunctions.m"];
  e*f^(a+b*x+c*x^2)/(2*c*Log[f]) -
  Dist[(b*e-2*c*d)/(2*c),Int[f^(a+b*x+c*x^2),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*f_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(17th)@ExponentialFunctions.m"];
  e*(d+e*x)^(m-1)*f^(a+b*x+c*x^2)/(2*c*Log[f]) -
  Dist[(m-1)*e^2/(2*c*Log[f]),Int[(d+e*x)^(m-2)*f^(a+b*x+c*x^2),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[m] && m>1 && ZeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*f_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(18th)@ExponentialFunctions.m"];
  e*(d+e*x)^(m-1)*f^(a+b*x+c*x^2)/(2*c*Log[f]) -
  Dist[(b*e-2*c*d)/(2*c),Int[(d+e*x)^(m-1)*f^(a+b*x+c*x^2),x]] -
  Dist[(m-1)*e^2/(2*c*Log[f]),Int[(d+e*x)^(m-2)*f^(a+b*x+c*x^2),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[m] && m>1 && NonzeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*f_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(19th)@ExponentialFunctions.m"];
  (d+e*x)^(m+1)*f^(a+b*x+c*x^2)/(e*(m+1)) -
  Dist[2*c*Log[f]/(e^2*(m+1)),Int[(d+e*x)^(m+2)*f^(a+b*x+c*x^2),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[m] && m<-1 && ZeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*f_^(a_.+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(20th)@ExponentialFunctions.m"];
  (d+e*x)^(m+1)*f^(a+b*x+c*x^2)/(e*(m+1)) -
  Dist[(b*e-2*c*d)*Log[f]/(e^2*(m+1)),Int[(d+e*x)^(m+1)*f^(a+b*x+c*x^2),x]] -
  Dist[2*c*Log[f]/(e^2*(m+1)),Int[(d+e*x)^(m+2)*f^(a+b*x+c*x^2),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && RationalQ[m] && m<-1 && NonzeroQ[b*e-2*c*d]

(* ::Code:: *)
Int[(a_.+b_.*x_)^m_*f_^((c_.+d_.*x_)^n_.),x_Symbol] :=
(Print["Int(21th)@ExponentialFunctions.m"];
  (a+b*x)^(m+1)*f^((c+d*x)^n)/(b*(m+1)) -
  Dist[d*n*Log[f]/(b*(m+1)),Int[(a+b*x)^(m+1)*f^((c+d*x)^n)*(c+d*x)^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && RationalQ[m] && m<-1 && IntegerQ[n] && n>1

(* ::Code:: *)
Int[1/(a_+b_.*f_^(c_.+d_.*x_)),x_Symbol] :=
(Print["Int(22th)@ExponentialFunctions.m"];
  -Log[b+a*f^(-c-d*x)]/(a*d*Log[f])) /;
FreeQ[{a,b,c,d,f},x] && NegativeCoefficientQ[d]

(* ::Code:: *)
Int[1/(a_+b_.*f_^(c_.+d_.*x_)),x_Symbol] :=
(Print["Int(23th)@ExponentialFunctions.m"];
  x/a-Log[a+b*f^(c+d*x)]/(a*d*Log[f])) /;
FreeQ[{a,b,c,d,f},x]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
(Print["Int(24th)@ExponentialFunctions.m"];
  -2*ArcTanh[Sqrt[a+b*f^(c+d*x)]/Sqrt[a]]/(Sqrt[a]*d*Log[f])) /;
FreeQ[{a,b,c,d,f},x] && PosQ[a]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
(Print["Int(25th)@ExponentialFunctions.m"];
  2*ArcTan[Sqrt[a+b*f^(c+d*x)]/Sqrt[-a]]/(Sqrt[-a]*d*Log[f])) /;
FreeQ[{a,b,c,d,f},x] && NegQ[a]

(* ::Code:: *)
Int[(a_+b_.*f_^(c_.+d_.*x_))^n_,x_Symbol] :=
(Print["Int(26th)@ExponentialFunctions.m"];
  (a+b*f^(c+d*x))^n/(n*d*Log[f]) + 
  Dist[a,Int[(a+b*f^(c+d*x))^(n-1),x]]) /;
FreeQ[{a,b,c,d,f},x] && FractionQ[n] && n>0

(* ::Code:: *)
Int[(a_+b_.*f_^(c_.+d_.*x_))^n_,x_Symbol] :=
(Print["Int(27th)@ExponentialFunctions.m"];
  -(a+b*f^(c+d*x))^(n+1)/((n+1)*a*d*Log[f]) + 
  Dist[1/a,Int[(a+b*f^(c+d*x))^(n+1),x]]) /;
FreeQ[{a,b,c,d,f},x] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[x_^m_./(a_+b_.*f_^(c_.+d_.*x_)), x_Symbol] :=
(Print["Int(28th)@ExponentialFunctions.m"];
  x^(m+1)/(a*(m+1)) -
  Dist[b/a,Int[x^m*f^(c+d*x)/(a+b*f^(c+d*x)),x]]) /;
FreeQ[{a,b,c,d,f},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*f_^(c_.+d_.*x_))^n_, x_Symbol] :=
(Print["Int(29th)@ExponentialFunctions.m"];
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(a+b*f^(c+d*x))^n,x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]]) /;
FreeQ[{a,b,c,d,f},x] && RationalQ[{m,n}] && m>0 && n<-1

(* ::Code:: *)
Int[x_^m_*f_^(c_.*(a_+b_.*x_)^2),x_Symbol] :=
(Print["Int(30th)@ExponentialFunctions.m"];
  Int[x^m*f^(a^2*c+2*a*b*c*x+b^2*c*x^2),x]) /;
FreeQ[{a,b,c,f},x] && FractionQ[m] && m>1

(* ::Code:: *)
Int[x_^m_.*f_^(c_.*(a_+b_.*x_)^n_),x_Symbol] :=
(Print["Int(31th)@ExponentialFunctions.m"];
  Dist[1/b^m,Int[Expand[b^m*x^m-(a+b*x)^m,x]*f^(c*(a+b*x)^n),x]] +
  Dist[1/b^(m+1),Subst[Int[x^m*f^(c*x^n),x],x,a+b*x]]) /;
FreeQ[{a,b,c,f,n},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*f_^(c_.+d_.*x_)/(a_+b_.*f_^(c_.+d_.*x_)), x_Symbol] :=
(Print["Int(32th)@ExponentialFunctions.m"];
  x^m*Log[1+b*f^(c+d*x)/a]/(b*d*Log[f]) -
  Dist[m/(b*d*Log[f]),Int[x^(m-1)*Log[1+b/a*f^(c+d*x)],x]]) /;
FreeQ[{a,b,c,d,f},x] && RationalQ[m] && m>=1

(* ::Code:: *)
Int[x_^m_.*f_^(c_.+d_.*x_)*(a_.+b_.*f_^v_)^n_,x_Symbol] :=
(Print["Int(33th)@ExponentialFunctions.m"];
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[f^(c+d*x)*(a+b*f^v)^n,x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]]) /;
FreeQ[{a,b,c,d,f},x] && ZeroQ[2*(c+d*x)-v] && RationalQ[m] && m>0 && IntegerQ[n] && n<0

(* ::Code:: *)
Int[x_^m_./(a_.*f_^(c_.+d_.*x_)+b_.*f_^v_),x_Symbol] :=
(Print["Int(34th)@ExponentialFunctions.m"];
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[1/(a*f^(c+d*x)+b*f^v),x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]]) /;
FreeQ[{a,b,c,d,f},x] && ZeroQ[(c+d*x)+v] && RationalQ[m] && m>0

(* ::Code:: *)
Int[(a_.+b_.*x_)^m_.*(f_^(e_.*(c_.+d_.*x_)^n_.))^p_.,x_Symbol] :=
(Print["Int(35th)@ExponentialFunctions.m"];
  Dist[1/b,Subst[Int[x^m*(f^(e*(c-a*d/b+d*x/b)^n))^p,x],x,a+b*x]]) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && RationalQ[p] && Not[a===0 && b===1]

(* ::Code:: *)
Int[f_^((a_.+b_.*x_^4)/x_^2),x_Symbol] :=
(Print["Int(36th)@ExponentialFunctions.m"];
  Sqrt[Pi]*Exp[2*Sqrt[-a*Log[f]]*Sqrt[-b*Log[f]]]*Erf[(Sqrt[-a*Log[f]]+Sqrt[-b*Log[f]]*x^2)/x]/
    (4*Sqrt[-b*Log[f]]) -
  Sqrt[Pi]*Exp[-2*Sqrt[-a*Log[f]]*Sqrt[-b*Log[f]]]*Erf[(Sqrt[-a*Log[f]]-Sqrt[-b*Log[f]]*x^2)/x]/
    (4*Sqrt[-b*Log[f]])) /;
FreeQ[{a,b,f},x]

(* ::Code:: *)
Int[1/(a_+b_.*f_^u_+c_.*f_^v_), x_Symbol] :=
(Print["Int(37th)@ExponentialFunctions.m"];
  x/a -
  Dist[1/a,Int[f^u*(b+c*f^u)/(a+b*f^u+c*f^v),x]]) /;
FreeQ[{a,b,c,f},x] && LinearQ[u,x] && LinearQ[v,x] && ZeroQ[2*u-v] &&
Not[RationalQ[Rt[b^2-4*a*c,2]]]

(* ::Code:: *)
Int[(d_+e_.*f_^u_)/(a_+b_.*f_^u_+c_.*f_^v_), x_Symbol] :=
(Print["Int(38th)@ExponentialFunctions.m"];
  d*x/a -
  Dist[1/a,Int[f^u*(b*d-a*e+c*d*f^u)/(a+b*f^u+c*f^v),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && LinearQ[u,x] && LinearQ[v,x] && ZeroQ[2*u-v] &&
Not[RationalQ[Rt[b^2-4*a*c,2]]]

(* ::Code:: *)
Int[u_/(a_+b_.*f_^v_+c_.*f_^w_), x_Symbol] :=
(Print["Int(39th)@ExponentialFunctions.m"];
  Int[u*f^v/(c+a*f^v+b*f^(2*v)),x]) /;
FreeQ[{a,b,c,f},x] && LinearQ[v,x] && LinearQ[w,x] && ZeroQ[v+w] &&
If[RationalQ[Coefficient[v,x,1]], Coefficient[v,x,1]>0, LeafCount[v]<LeafCount[w]]

(* ::Code:: *)
Int[x_^m_.*(E^x_+x_^m_.)^n_,x_Symbol] :=
(Print["Int(40th)@ExponentialFunctions.m"];
  -(E^x+x^m)^(n+1)/(n+1) +
  Int[(E^x+x^m)^(n+1),x] +
  Dist[m,Int[x^(m-1)*(E^x+x^m)^n,x]]) /;
RationalQ[{m,n}] && m>0 && NonzeroQ[n+1]
