(* ::Package:: *)

(* ::Code:: *)
Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(1th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  -2*ArcTanh[b/q+2*c*x/q]/q /;
 RationalQ[q] || SqrtNumberQ[q] && RationalQ[b/q]]) /;
FreeQ[{a,b,c},x] && PosQ[b^2-4*a*c]

(* ::Code:: *)
Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(2th)@RationalFunctionsOfTrinomials.m"];
  -2*ArcTanh[(b+2*c*x)/Rt[b^2-4*a*c,2]]/Rt[b^2-4*a*c,2]) /;
FreeQ[{a,b,c},x] && PosQ[b^2-4*a*c]

(* ::Code:: *)
Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(3th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[4*a*c-b^2,2]},
  2*ArcTan[b/q+2*c*x/q]/q /;
 RationalQ[q] || SqrtNumberQ[q] && RationalQ[b/q]]) /;
FreeQ[{a,b,c},x] && NegQ[b^2-4*a*c]

(* ::Code:: *)
Int[1/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(4th)@RationalFunctionsOfTrinomials.m"];
  2*ArcTan[(b+2*c*x)/Rt[4*a*c-b^2,2]]/Rt[4*a*c-b^2,2]) /;
FreeQ[{a,b,c},x] && NegQ[b^2-4*a*c]

(* ::Code:: *)
Int[(a_+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(5th)@RationalFunctionsOfTrinomials.m"];
  Int[(b/2+c*x)^(2*n),x]/c^n) /;
FreeQ[{a,b,c},x] && IntegerQ[n] && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(a_+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(6th)@RationalFunctionsOfTrinomials.m"];
  (b+2*c*x)*(a+b*x+c*x^2)^(n+1)/((n+1)*(b^2-4*a*c)) -
  Dist[2*c*(2*n+3)/((n+1)*(b^2-4*a*c)),Int[(a+b*x+c*x^2)^(n+1),x]]) /;
FreeQ[{a,b,c},x] && IntegerQ[n] && n<-1 && NonzeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(7th)@RationalFunctionsOfTrinomials.m"];
  e*Log[-a-b*x-c*x^2]/(2*c)) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[2*c*d-b*e] && NegativeCoefficientQ[a]

(* ::Code:: *)
Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(8th)@RationalFunctionsOfTrinomials.m"];
  e*Log[a+b*x+c*x^2]/(2*c)) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[2*c*d-b*e]

(* ::Code:: *)
Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(9th)@RationalFunctionsOfTrinomials.m"];
  e*Log[-a-b*x-c*x^2]/(2*c) +
  Dist[Simplify[(2*c*d-b*e)/(2*c)],Int[1/(a+b*x+c*x^2),x]]) /;
FreeQ[{a,b,c,d,e},x] && Not[RationalQ[Rt[b^2-4*a*c,2]]] && NonzeroQ[a*e^2+c*d^2-b*d*e] && 
NegativeCoefficientQ[a]

(* ::Code:: *)
Int[(d_.+e_.*x_)/(a_+b_.*x_+c_.*x_^2),x_Symbol] :=
(Print["Int(10th)@RationalFunctionsOfTrinomials.m"];
  e*Log[a+b*x+c*x^2]/(2*c) +
  Dist[Simplify[(2*c*d-b*e)/(2*c)],Int[1/(a+b*x+c*x^2),x]]) /;
FreeQ[{a,b,c,d,e},x] && Not[RationalQ[Rt[b^2-4*a*c,2]]] && NonzeroQ[a*e^2+c*d^2-b*d*e]

(* ::Code:: *)
Int[(d_+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^n_.,x_Symbol] :=
(Print["Int(11th)@RationalFunctionsOfTrinomials.m"];
  Int[(d+e*x)^(m+n)*(a/d+c/e*x)^n,x]) /;
FreeQ[{a,b,c,d,e,m},x] && ZeroQ[a*e^2-b*d*e+c*d^2] && IntegerQ[n]

(* ::Code:: *)
Int[(d_+e_.*x_)^m_.*(a_+c_.*x_^2)^n_.,x_Symbol] :=
(Print["Int(12th)@RationalFunctionsOfTrinomials.m"];
  Int[(d+e*x)^(m+n)*(a/d+c/e*x)^n,x]) /;
FreeQ[{a,c,d,e,m},x] && ZeroQ[a*e^2+c*d^2] && IntegerQ[n]

(* ::Code:: *)
Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(13th)@RationalFunctionsOfTrinomials.m"];
  e*(d+e*x)^m*(a+c*x^2)^(n+1)/(2*c*d*(n+1))) /;
FreeQ[{a,c,d,e,m,n},x] && ZeroQ[a*e^2+c*d^2] && ZeroQ[m+2*(n+1)] && Not[IntegerQ[n]]

(* ::Code:: *)
Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(14th)@RationalFunctionsOfTrinomials.m"];
  -e*(d+e*x)^m*(a+c*x^2)^(n+1)/(2*c*d*(m+n+1)) +
  Dist[(m+2*(n+1))/(2*d*(m+n+1)),Int[(d+e*x)^(m+1)*(a+c*x^2)^n,x]]) /;
FreeQ[{a,c,d,e,n},x] && ZeroQ[a*e^2+c*d^2] && NonzeroQ[m+n+1] && NonzeroQ[m+2*(n+1)] && 
  RationalQ[m] && m<-1 && Not[IntegerQ[n]]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(15th)@RationalFunctionsOfTrinomials.m"];
  -e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(n+1)/(c*(m-1)) +
  Dist[e^2/c,Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^(n+1),x]]) /;
FreeQ[{a,b,c,d,e},x] && RationalQ[{m,n}] && n<-1 && ZeroQ[m+2*n+1] && ZeroQ[2*c*d-b*e]

(* ::Code:: *)
Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(16th)@RationalFunctionsOfTrinomials.m"];
  e*(a+b*x+c*x^2)^(n+1)/(2*c*(n+1))) /;
FreeQ[{a,b,c,d,e,n},x] && ZeroQ[2*c*d-b*e] && NonzeroQ[n+1]

(* ::Code:: *)
Int[(d_.+e_.*x_)*(a_.+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(17th)@RationalFunctionsOfTrinomials.m"];
  e*(a+b*x+c*x^2)^(n+1)/(2*c*(n+1)) +
  Dist[(2*c*d-b*e)/(2*c),Int[(a+b*x+c*x^2)^n,x]]) /;
FreeQ[{a,b,c,d,e,n},x] && NonzeroQ[n+1] && Not[IntegerQ[n] && n>0] && NonzeroQ[2*c*d-b*e]

(* ::Code:: *)
Int[(d_+e_.*x_)*(a_.+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(18th)@RationalFunctionsOfTrinomials.m"];
  e*(a+c*x^2)^(n+1)/(2*c*(n+1)) +
  Dist[d,Int[(a+c*x^2)^n,x]]) /;
FreeQ[{a,c,d,e,n},x] && NonzeroQ[n+1] && Not[IntegerQ[n] && n>0]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*(a_.+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(19th)@RationalFunctionsOfTrinomials.m"];
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(n+1)/(c*(m+2*n+1)) -
  Dist[(a*e^2-b*d*e+c*d^2)*(m-1)/(c*(m+2*n+1)),Int[(d+e*x)^(m-2)*(a+b*x+c*x^2)^n,x]]) /;
FreeQ[{a,b,c,d,e,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+2*n+1] && Not[IntegerQ[n] && n>=-1] && 
(ZeroQ[m+n] || ZeroQ[2*c*d-b*e])

(* ::Code:: *)
Int[(d_+e_.*x_)^m_*(a_.+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(20th)@RationalFunctionsOfTrinomials.m"];
  -e*(d+e*x)^(m-1)/(c*(m-1)*(a+c*x^2)^(m-1)) +
  Dist[(a*e^2+c*d^2)/c,Int[(d+e*x)^(m-2)/(a+c*x^2)^m,x]]) /;
FreeQ[{a,c,d,e,n},x] && RationalQ[m] && m>1 && ZeroQ[m+n]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_.*(a_.+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(21th)@RationalFunctionsOfTrinomials.m"];
  e*(d+e*x)^(m-1)*(a+b*x+c*x^2)^(n+1)/(c*(m+2*n+1)) +
  Dist[(2*c*d-b*e)*(m+n)/(c*(m+2*n+1)),Int[(d+e*x)^(m-1)*(a+b*x+c*x^2)^n,x]]) /;
FreeQ[{a,b,c,d,e,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+2*n+1] && Not[IntegerQ[n] && n>=-1] &&
ZeroQ[a*e^2-b*d*e+c*d^2]

(* ::Code:: *)
Int[(d_+e_.*x_)^m_.*(a_.+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(22th)@RationalFunctionsOfTrinomials.m"];
  e*(d+e*x)^(m-1)*(a+c*x^2)^(n+1)/(c*(m+2*n+1)) +
  Dist[2*c*d*(m+n)/(c*(m+2*n+1)),Int[(d+e*x)^(m-1)*(a+c*x^2)^n,x]]) /;
FreeQ[{a,c,d,e,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+2*n+1] && Not[IntegerQ[n] && n>=-1] &&
ZeroQ[a*e^2+c*d^2]

(* ::Code:: *)
Int[x_^m_*(b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(23th)@RationalFunctionsOfTrinomials.m"];
  x^m*(b*x+c*x^2)^(n+1)/(b*(m+n+1))) /;
FreeQ[{b,c,m,n},x] && NonzeroQ[m+n+1] && ZeroQ[m+2*(n+1)]

(* ::Code:: *)
Int[x_^m_*(b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(24th)@RationalFunctionsOfTrinomials.m"];
  x^m*(b*x+c*x^2)^(n+1)/(b*(m+n+1)) -
  Dist[c*(m+2*(n+1))/(b*(m+n+1)),Int[x^(m+1)*(b*x+c*x^2)^n,x]]) /;
FreeQ[{b,c,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+1] && Not[IntegerQ[n] && n>=-1]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_*(a_+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(25th)@RationalFunctionsOfTrinomials.m"];
  e*(d+e*x)^(m+1)*(a+b*x+c*x^2)^(n+1)/((m+1)*(a*e^2-b*d*e+c*d^2)) +
  Dist[(2*c*d-b*e)*(m+n+2)/((m+1)*(a*e^2-b*d*e+c*d^2)),Int[(d+e*x)^(m+1)*(a+b*x+c*x^2)^n,x]]) /;
FreeQ[{a,b,c,d,e,n},x] && RationalQ[m] && m<-1 && NonzeroQ[a*e^2-b*d*e+c*d^2] && 
Not[IntegerQ[n] && n>=-1] && ZeroQ[m+2*n+3]

(* ::Code:: *)
Int[(d_+e_.*x_)^m_*(a_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(26th)@RationalFunctionsOfTrinomials.m"];
  e*(d+e*x)^(m+1)*(a+c*x^2)^(n+1)/((m+1)*(a*e^2+c*d^2)) +
  Dist[2*c*d*(m+n+2)/((m+1)*(a*e^2+c*d^2)),Int[(d+e*x)^(m+1)*(a+c*x^2)^n,x]]) /;
FreeQ[{a,c,d,e,n},x] && RationalQ[m] && m<-1 && NonzeroQ[a*e^2+c*d^2] && 
Not[IntegerQ[n] && n>=-1] && ZeroQ[m+2*n+3]

(* ::Code:: *)
Int[1/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
(Print["Int(27th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[a/c,2]},
  Dist[c*q/(2*a),Int[(q+x^2)/(a+b*x^2+c*x^4),x]] +
  Dist[c*q/(2*a),Int[(q-x^2)/(a+b*x^2+c*x^4),x]]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PosQ[a/c] && 
(NegativeQ[b^2-4*a*c] || RationalQ[a/c] && Not[PositiveQ[b^2-4*a*c]])

(* ::Code:: *)
Int[1/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
(Print["Int(28th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[-a/c,2]},
  -Dist[c*q/(2*a),Int[(q+x^2)/(a+b*x^2+c*x^4),x]] -
  Dist[c*q/(2*a),Int[(q-x^2)/(a+b*x^2+c*x^4),x]]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && NegQ[a/c] &&
(NegativeQ[b^2-4*a*c] || RationalQ[a/c] && Not[PositiveQ[b^2-4*a*c]])

(* ::Code:: *)
Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
(Print["Int(29th)@RationalFunctionsOfTrinomials.m"];
  d/(a*Rt[-(b*d+2*a*e)/(a*d),2])*ArcTanh[d*Rt[-(b*d+2*a*e)/(a*d),2]*x/(d-e*x^2)]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-a*e^2] && NegQ[(b*d+2*a*e)/(a*d)]

(* ::Code:: *)
(* Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
(Print["Int(30th)@RationalFunctionsOfTrinomials.m"];
  d/(a*Rt[(b*d+2*a*e)/(a*d),2])*ArcTan[d*Rt[(b*d+2*a*e)/(a*d),2]*x/(d-e*x^2)]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-a*e^2] && PosQ[(b*d+2*a*e)/(a*d)] *)

(* ::Code:: *)
Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
(Print["Int(31th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=c*d/e},
  Module[{r=Rt[2*c*q-b*c,2]},
  Dist[e/2,Int[1/(q-r*x+c*x^2),x]] + 
  Dist[e/2,Int[1/(q+r*x+c*x^2),x]]] /;
 Not[NegativeQ[2*c*q-b*c]]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[c*d^2-a*e^2] && PosQ[(b*d+2*a*e)/(a*d)]

(* ::Code:: *)
Int[(d_.+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
(Print["Int(32th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[a/c,2]},
  Dist[(q*c*d+a*e)/(2*a),Int[(q+x^2)/(a+b*x^2+c*x^4),x]] +
  Dist[(q*c*d-a*e)/(2*a),Int[(q-x^2)/(a+b*x^2+c*x^4),x]]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-a*e^2] && PosQ[a/c] &&
(NegativeQ[b^2-4*a*c] || RationalQ[a/c] && Not[PositiveQ[b^2-4*a*c]])

(* ::Code:: *)
Int[(d_+e_.*x_^2)/(a_+b_.*x_^2+c_.*x_^4), x_Symbol] :=
(Print["Int(33th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[-a/c,2]},
  Dist[-(q*c*d-a*e)/(2*a),Int[(q+x^2)/(a+b*x^2+c*x^4),x]] -
  Dist[(q*c*d+a*e)/(2*a),Int[(q-x^2)/(a+b*x^2+c*x^4),x]]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[c*d^2-a*e^2] && NegQ[a/c] &&
(NegativeQ[b^2-4*a*c] || RationalQ[a/c] && Not[PositiveQ[b^2-4*a*c]])

(* ::Code:: *)
Int[1/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(34th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q-b*c,2]},
  Dist[q/(2*a*r),Int[(r-c*x^(n/2))/(q-r*x^(n/2)+c*x^n),x]] + 
  Dist[q/(2*a*r),Int[(r+c*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]]] /;
 Not[NegativeQ[2*c*q-b*c]]]) /;
FreeQ[{a,b,c},x] && NegativeQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegerQ[n/2] && n>2 && 
  NegativeQ[b^2-4*a*c] && PosQ[a*c]

(* ::Code:: *)
Int[1/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(35th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Dist[2*c/q,Int[1/(b-q+2*c*x^n),x]] -
  Dist[2*c/q,Int[1/(b+q+2*c*x^n),x]]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegerQ[n] && n>1 && 
  Not[IntegerQ[n/2] && NegativeQ[b^2-4*a*c] && PosQ[a*c]]

(* ::Code:: *)
Int[1/(x_*(a_+b_.*x_^n_+c_.*x_^j_)),x_Symbol] :=
(Print["Int(36th)@RationalFunctionsOfTrinomials.m"];
  Log[x]/a - Dist[1/a,Int[x^(n-1)*(b+c*x^n)/(a+b*x^n+c*x^(2*n)),x]]) /;
FreeQ[{a,b,c,n},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && Not[NegativeQ[n]]

(* ::Code:: *)
Int[x_^m_/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(37th)@RationalFunctionsOfTrinomials.m"];
  x^(m+1)/(a*(m+1)) -
  Dist[1/a,Int[x^(m+n)*(b+c*x^n)/(a+b*x^n+c*x^(2*n)),x]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n] && n>0 && m<-1

(* ::Code:: *)
Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(38th)@RationalFunctionsOfTrinomials.m"];
  x^(m-2*n+1)/(c*(m-2*n+1)) -
  Dist[1/c,Int[x^(m-2*n)*(a+b*x^n)/(a+b*x^n+c*x^(2*n)),x]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n] && 0<2*n<=m

(* ::Code:: *)
Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(39th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q-b*c,2]},
  Dist[c/(2*r),Int[x^(m-n/2)/(q-r*x^(n/2)+c*x^n),x]] - 
  Dist[c/(2*r),Int[x^(m-n/2)/(q+r*x^(n/2)+c*x^n),x]]] /;
 Not[NegativeQ[2*c*q-b*c]]]) /;
FreeQ[{a,b,c},x] && NegativeQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n/2] && 
  1<n/2<=m<2*n && CoprimeQ[m+1,n] && PosQ[a*c]

(* ::Code:: *)
Int[x_^m_./(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(40th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Dist[2*c/q,Int[x^m/(b-q+2*c*x^n),x]] -
  Dist[2*c/q,Int[x^m/(b+q+2*c*x^n),x]]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n] && 0<m<n && 
  CoprimeQ[m+1,n] && Not[IntegerQ[n/2] && NegativeQ[b^2-4*a*c] && PosQ[a*c]]

(* ::Code:: *)
Int[x_^m_/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(41th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Dist[1-b/q,Int[x^(m-n)/(b-q+2*c*x^n),x]] +
  Dist[1+b/q,Int[x^(m-n)/(b+q+2*c*x^n),x]]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n] && n<m<2*n && 
  CoprimeQ[m+1,n] && Not[IntegerQ[n/2] && NegativeQ[b^2-4*a*c] && PosQ[a*c]]

(* ::Code:: *)
Int[(d_.+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(42th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q-b*c,2]},
  Dist[c/(2*q*r),Int[(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x]] + 
  Dist[c/(2*q*r),Int[(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]]] /;
 Not[NegativeQ[2*c*q-b*c]]]) /;
FreeQ[{a,b,c,d,e},x] && NegativeQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegerQ[n/2] && n>2 && PosQ[a*c]

(* ::Code:: *)
Int[(d_.+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(43th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Dist[(e+(2*c*d-b*e)/q),Int[1/(b-q+2*c*x^n),x]] +
  Dist[(e-(2*c*d-b*e)/q),Int[1/(b+q+2*c*x^n),x]]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegerQ[n] && n>1 && 
  Not[IntegerQ[n/2] && NegativeQ[b^2-4*a*c] && PosQ[a*c]]

(* ::Code:: *)
Int[(d_+e_.*x_^n_)/(x_*(a_+b_.*x_^n_+c_.*x_^j_)),x_Symbol] :=
(Print["Int(44th)@RationalFunctionsOfTrinomials.m"];
  d*Log[x]/a - Dist[1/a,Int[x^(n-1)*(b*d-a*e+c*d*x^n)/(a+b*x^n+c*x^(2*n)),x]]) /;
FreeQ[{a,b,c,d,e,n},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n]

(* ::Code:: *)
Int[x_^m_*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(45th)@RationalFunctionsOfTrinomials.m"];
  d*x^(m+1)/(a*(m+1)) -
  Dist[1/a,Int[x^(m+n)*(b*d-a*e+c*d*x^n)/(a+b*x^n+c*x^(2*n)),x]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n] && n>0 && m<-1

(* ::Code:: *)
Int[x_^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(46th)@RationalFunctionsOfTrinomials.m"];
  e*x^(m-n+1)/(c*(m-n+1)) -
  Dist[1/c,Int[x^(m-n)*(a*e+(b*e-c*d)*x^n)/(a+b*x^n+c*x^(2*n)),x]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n] && 0<n<=m

(* ::Code:: *)
Int[x_^m_*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(47th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[a*c,2]},
  Module[{r=Rt[2*c*q-b*c,2]},
  Dist[c/(2*q*r),Int[x^m*(d*r-(c*d-e*q)*x^(n/2))/(q-r*x^(n/2)+c*x^n),x]] + 
  Dist[c/(2*q*r),Int[x^m*(d*r+(c*d-e*q)*x^(n/2))/(q+r*x^(n/2)+c*x^n),x]]] /;
 Not[NegativeQ[2*c*q-b*c]]]) /;
FreeQ[{a,b,c,d,e},x] && NegativeQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n/2] && 
  0<m<n && CoprimeQ[m+1,n] && PosQ[a*c]

(* ::Code:: *)
Int[x_^m_.*(d_+e_.*x_^n_)/(a_+b_.*x_^n_+c_.*x_^j_),x_Symbol] :=
(Print["Int(48th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Dist[(e+(2*c*d-b*e)/q),Int[x^m/(b-q+2*c*x^n),x]] +
  Dist[(e-(2*c*d-b*e)/q),Int[x^m/(b+q+2*c*x^n),x]]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n] && 
  0<m<n && CoprimeQ[m+1,n] && Not[IntegerQ[n/2] && NegativeQ[b^2-4*a*c] && PosQ[a*c]]

(* ::Code:: *)
Int[(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(49th)@RationalFunctionsOfTrinomials.m"];
  Dist[1/c^p,Int[(b/2+c*x^n)^(2*p),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegersQ[n,p] && n>1 && p<0 && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(50th)@RationalFunctionsOfTrinomials.m"];
  -x*(b^2-2*a*c+b*c*x^n)*(a+b*x^n+c*x^j)^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) +
  Dist[1/(a*n*(p+1)*(b^2-4*a*c)),
    Int[(b^2-2*a*c+n*(p+1)*(b^2-4*a*c)+b*c*(n*(2*p+3)+1)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegerQ[n] && n>1 && RationalQ[p] && p<-1 && 
NonzeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(51th)@RationalFunctionsOfTrinomials.m"];
  Dist[1/c^p,Int[x^m*(b/2+c*x^n)^(2*p),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegersQ[m,n,p] && n>1 && p<0 && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_.+c_.*x_^j_)^p_.,x_Symbol] :=
(Print["Int(52th)@RationalFunctionsOfTrinomials.m"];
  x^(m-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(2*n*p+m+1)) - 
  Dist[1/(c*(2*n*p+m+1)),
    Int[x^(m-2*n)*Sim[a*(m-2*n+1)+(b*(n*p-n+m+1))*x^n,x]*(a+b*x^n+c*x^(2*n))^p,x]]) /;
FreeQ[{a,b,c,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n] && 0<n<=m

(* ::Code:: *)
Int[x_^m_*(a_+b_.*x_^n_.+c_.*x_^j_.)^p_,x_Symbol] :=
(Print["Int(53th)@RationalFunctionsOfTrinomials.m"];
  x^(m+1)*(a+b*x^n+c*x^j)^(p+1)/(a*(m+1)) +
  Dist[c/a,Int[x^(m+2*n)*(a+b*x^n+c*x^j)^p,x]]) /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && IntegersQ[m,n] && m<-1 && n>0 && ZeroQ[m+n*(p+1)+1] &&
Not[IntegerQ[p] && p>0]

(* ::Code:: *)
Int[x_^m_*(a_+b_.*x_^n_.+c_.*x_^j_.)^p_,x_Symbol] :=
(Print["Int(54th)@RationalFunctionsOfTrinomials.m"];
  x^(m+1)*(a+b*x^n+c*x^j)^(p+1)/(a*(m+1)) -
  Dist[b/(2*a),Int[x^(m+n)*(a+b*x^n+c*x^j)^p,x]]) /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && IntegersQ[m,n] && m<-1 && n>0 && ZeroQ[m+2*n*(p+1)+1] &&
Not[IntegerQ[p] && p>0]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(55th)@RationalFunctionsOfTrinomials.m"];
  Dist[1/(m+1),Subst[Int[(a+b*x^(n/(m+1))+c*x^(2*n/(m+1)))^p,x],x,x^(m+1)]]) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && NonzeroQ[m+1] && 
  IntegersQ[p,n/(m+1)] && Not[NegativeQ[m+1]] && p<0

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(56th)@RationalFunctionsOfTrinomials.m"];
  Dist[1/n,Subst[Int[x^((m+1)/n-1)*(a+b*x+c*x^2)^p,x],x,x^n]]) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[p,(m+1)/n] && 
  Not[NegativeQ[n]] && p<0 && ((m+1)/n>0 || Not[IntegerQ[m]])

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
  Module[{g=GCD[m+1,n]},
  Dist[1/g,Subst[Int[x^((m+1)/g-1)*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g]]] /; 
FreeQ[{a,b,c,m,n},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && NonzeroQ[m+1] && 
  IntegersQ[m,n,p] && Not[CoprimeQ[m+1,n]] && p<0 && (m+1)/n>0

(* ::Code:: *)
Int[(d_.+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(58th)@RationalFunctionsOfTrinomials.m"];
  Dist[1/c^p,Int[(d+e*x^n)*(b/2+c*x^n)^(2*p),x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && IntegersQ[n,p] && n>1 && p<0 && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(d_.+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(59th)@RationalFunctionsOfTrinomials.m"];
  x*(a*b*e-b^2*d+2*a*c*d+c*(2*a*e-b*d)*x^n)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*n*(p+1)*(b^2-4*a*c)) -
  Dist[1/(a*n*(p+1)*(b^2-4*a*c)),
    Int[(a*b*e-b^2*d+2*a*c*d-d*n*(p+1)*(b^2-4*a*c)+c*(2*a*e-b*d)*(n*(2*p+3)+1)*x^n)*
      (a+b*x^n+c*x^(2*n))^(p+1),x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && IntegerQ[n] && n>1 && RationalQ[p] && p<-1 && 
NonzeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[x_^m_.*(d_+e_.*x_^n_.)*(a_+b_.*x_^n_.+c_.*x_^j_)^p_.,x_Symbol] :=
(Print["Int(60th)@RationalFunctionsOfTrinomials.m"];
  e*x^(m-n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(2*n*p+n+m+1)) - 
  Dist[1/(c*(2*n*p+n+m+1)),
    Int[x^(m-n)*Sim[a*e*(m-n+1)+(b*e*(n*p+m+1)-c*d*(2*n*p+n+m+1))*x^n,x]*(a+b*x^n+c*x^(2*n))^p,x]]) /;
FreeQ[{a,b,c,d,e,p},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[m,n] && 0<n<=m

(* ::Code:: *)
Int[x_^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(61th)@RationalFunctionsOfTrinomials.m"];
  Dist[1/(m+1),Subst[Int[(d+e*x^(n/(m+1)))*(a+b*x^(n/(m+1))+c*x^(2*n/(m+1)))^p,x],x,x^(m+1)]]) /;
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && NonzeroQ[m+1] && 
  IntegersQ[p,n/(m+1)] && Not[NegativeQ[m+1]] && p<0

(* ::Code:: *)
Int[x_^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(62th)@RationalFunctionsOfTrinomials.m"];
  Dist[1/n,Subst[Int[x^((m+1)/n-1)*(d+e*x)*(a+b*x+c*x^2)^p,x],x,x^n]]) /;
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && IntegersQ[p,(m+1)/n] && 
  Not[NegativeQ[n]] && p<0 && ((m+1)/n>0 || Not[IntegerQ[m]])

(* ::Code:: *)
Int[x_^m_.*(d_+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
  Module[{g=GCD[m+1,n]},
  Dist[1/g,Subst[Int[x^((m+1)/g-1)*(d+e*x^(n/g))*(a+b*x^(n/g)+c*x^(2*n/g))^p,x],x,x^g]]] /; 
FreeQ[{a,b,c,d,e,m,n},x] && NonzeroQ[b^2-4*a*c] && ZeroQ[j-2*n] && NonzeroQ[m+1] && 
  IntegersQ[m,n,p] && Not[CoprimeQ[m+1,n]] && p<0 && (m+1)/n>0

(* ::Code:: *)
Int[(a_+b_.*x_^n_)/(c_+d_.*x_^2+e_.*x_^n_+f_.*x_^j_), x_Symbol] :=
(Print["Int(64th)@RationalFunctionsOfTrinomials.m"];
  a/Rt[c*d,2]*ArcTan[(n-1)*a*Rt[c*d,2]*x/(c*(a*(n-1)-b*x^n))]) /;
FreeQ[{a,b,c,d,e,f,n},x] && ZeroQ[j-2*n] &&
ZeroQ[b^2*c-a^2*f*(n-1)^2] && ZeroQ[b*e+2*a*f*(n-1)] && PosQ[c*d]

(* ::Code:: *)
Int[(a_+b_.*x_^n_)/(c_+d_.*x_^2+e_.*x_^n_+f_.*x_^j_), x_Symbol] :=
(Print["Int(65th)@RationalFunctionsOfTrinomials.m"];
  a/Rt[-c*d,2]*ArcTanh[a*(n-1)*Rt[-c*d,2]*x/(c*(a*(n-1)-b*x^n))]) /;
FreeQ[{a,b,c,d,e,f,n},x] && ZeroQ[j-2*n] &&
ZeroQ[b^2*c-a^2*f*(n-1)^2] && ZeroQ[b*e+2*a*f*(n-1)] && NegQ[c*d]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_.)/(c_+d_.*x_^k_.+e_.*x_^n_.+f_.*x_^j_), x_Symbol] :=
(Print["Int(66th)@RationalFunctionsOfTrinomials.m"];
  a*ArcTan[a*(m-n+1)*Rt[c*d,2]*x^(m+1)/(c*(a*(m-n+1)+b*(m+1)*x^n))]/((m+1)*Rt[c*d,2])) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[j-2*n] && ZeroQ[k-2*(m+1)] &&
ZeroQ[a^2*f*(m-n+1)^2-b^2*c*(m+1)^2] && ZeroQ[b*e*(m+1)-2*a*f*(m-n+1)] && PosQ[c*d]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_.)/(c_+d_.*x_^k_.+e_.*x_^n_.+f_.*x_^j_), x_Symbol] :=
(Print["Int(67th)@RationalFunctionsOfTrinomials.m"];
  a*ArcTanh[a*(m-n+1)*Rt[-c*d,2]*x^(m+1)/(c*(a*(m-n+1)+b*(m+1)*x^n))]/((m+1)*Rt[-c*d,2])) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && ZeroQ[j-2*n] && ZeroQ[k-2*(m+1)] &&
ZeroQ[a^2*f*(m-n+1)^2-b^2*c*(m+1)^2] && ZeroQ[b*e*(m+1)-2*a*f*(m-n+1)] && NegQ[c*d]

(* ::Code:: *)
Int[(d_.+e_.*x_+f_.*x_^2+g_.*x_^3)/(a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4),x_Symbol] :=
(Print["Int(68th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  Dist[1/q,Int[(b*d-2*a*e+2*a*g+d*q+(2*a*d-2*a*f+b*g+g*q)*x)/(2*a+(b+q)*x+2*a*x^2),x]] -
  Dist[1/q,Int[(b*d-2*a*e+2*a*g-d*q+(2*a*d-2*a*f+b*g-g*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]]]) /;
FreeQ[{a,b,c,d,e,f,g},x] && PosQ[8*a^2+b^2-4*a*c]

(* ::Code:: *)
Int[(d_.+e_.*x_+g_.*x_^3)/(a_+b_.*x_+c_.*x_^2+b_.*x_^3+a_.*x_^4),x_Symbol] :=
(Print["Int(69th)@RationalFunctionsOfTrinomials.m"];
  Module[{q=Sqrt[8*a^2+b^2-4*a*c]},
  Dist[1/q,Int[(b*d-2*a*e+2*a*g+d*q+(2*a*d+b*g+g*q)*x)/(2*a+(b+q)*x+2*a*x^2),x]] -
  Dist[1/q,Int[(b*d-2*a*e+2*a*g-d*q+(2*a*d+b*g-g*q)*x)/(2*a+(b-q)*x+2*a*x^2),x]]]) /;
FreeQ[{a,b,c,d,e,g},x] && PosQ[8*a^2+b^2-4*a*c]

(* ::Code:: *)
If[ShowSteps,

Int[u_*v_^p_,x_Symbol] :=
(Print["Int(70th)@RationalFunctionsOfTrinomials.m"];
  Module[{m=Exponent[u,x],n=Exponent[v,x]},
  Module[{c=Coefficient[u,x,m]/(Coefficient[v,x,n]*(m+1+n*p)),w},
  w=Apart[u-c*x^(m-n)*((m-n+1)*v+(p+1)*x*D[v,x]),x];
  If[ZeroQ[w],
    ShowStep["
If p>1, 1<n<=m+1, and m+1-n*p<0, let c=pm/(qn*(m+1-n*p)), then if (Pm[x]-c*x^(m-n)*((m-n+1)*Qn[x]+(1-p)*x*D[Qn[x],x]))==0,",
	  "Int[Pm[x]/Qn[x]^p,x]", "c*x^(m-n+1)/Qn[x]^(p-1)",
      Hold[c*x^(m-n+1)*v^(p+1)]],
  ShowStep["If p>1, 1<n<=m+1, and m+1-n*p<0, let c=pm/(qn*(m+1-n*p)), then",
	"Int[Pm[x]/Qn[x]^p,x]",
	"c*x^(m-n+1)/Qn[x]^(p-1)+Int[(Pm[x]-c*x^(m-n)*((m-n+1)*Qn[x]+(1-p)*x*D[Qn[x],x]))/Qn[x]^p,x]",
	Hold[c*x^(m-n+1)*v^(p+1) + Int[w*v^p,x]]]]] /;
 m+1>=n>1 && m+n*p<-1 && FalseQ[DerivativeDivides[v,u,x]]]) /;
SimplifyFlag && RationalQ[p] && p<-1 && PolynomialQ[u,x] && PolynomialQ[v,x] && SumQ[v] && 
Not[MonomialQ[u,x] && BinomialQ[v,x]] && 
Not[ZeroQ[Coefficient[u,x,0]] && ZeroQ[Coefficient[v,x,0]]],

Int[u_*v_^p_,x_Symbol] :=
(Print["Int(71th)@RationalFunctionsOfTrinomials.m"];
  Module[{m=Exponent[u,x],n=Exponent[v,x]},
  Module[{c=Coefficient[u,x,m]/(Coefficient[v,x,n]*(m+1+n*p)),w},
  c=Coefficient[u,x,m]/(Coefficient[v,x,n]*(m+1+n*p));
  w=Apart[u-c*x^(m-n)*((m-n+1)*v+(p+1)*x*D[v,x]),x];
  If[ZeroQ[w],
    c*x^(m-n+1)*v^(p+1),
  c*x^(m-n+1)*v^(p+1) + Int[w*v^p,x]]] /;
 m+1>=n>1 && m+n*p<-1 && FalseQ[DerivativeDivides[v,u,x]]]) /;
RationalQ[p] && p<-1 && PolynomialQ[u,x] && PolynomialQ[v,x] && SumQ[v] && 
Not[MonomialQ[u,x] && BinomialQ[v,x]] && 
Not[ZeroQ[Coefficient[u,x,0]] && ZeroQ[Coefficient[v,x,0]]]]

(* ::Code:: *)
Int[f_'[u_]*g_[v_]*w_. + f_[u_]*g_'[v_]*t_.,x_Symbol] :=
(Print["Int(72th)@RationalFunctionsOfTrinomials.m"];
  f[u]*g[v]) /;
FreeQ[{f,g},x] && ZeroQ[w-D[u,x]] && ZeroQ[t-D[v,x]]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(73th)@RationalFunctionsOfTrinomials.m"];
  If[SplitFreeTerms[u,x][[1]]===0,
    ShowStep["","Int[a*u+b*v+\[CenterEllipsis],x]","a*Int[u,x]+b*Int[v,x]+\[CenterEllipsis]",Hold[
    SplitFreeIntegrate[u,x]]],
  ShowStep["","Int[a+b*u+c*v+\[CenterEllipsis],x]","a*x+b*Int[u,x]+c*Int[v,x]+\[CenterEllipsis]",Hold[
  SplitFreeIntegrate[u,x]]]]) /;
SimplifyFlag && SumQ[u],

Int[u_,x_Symbol] :=
(Print["Int(74th)@RationalFunctionsOfTrinomials.m"];
  SplitFreeIntegrate[u,x]) /;
SumQ[u]]

(* ::Code:: *)
SplitFreeIntegrate[u_,x_Symbol] :=
  If[SumQ[u],
    Map[Function[SplitFreeIntegrate[#,x]],u],
  If[FreeQ[u,x],
    u*x,
  If[MatchQ[u,c_*(a_+b_.*x) /; FreeQ[{a,b,c},x]],
    Int[u,x],
  Module[{lst=SplitFreeFactors[u,x]},
  Dist[lst[[1]], Int[lst[[2]],x]]]]]]
