(* ::Package:: *)

(* ::Code:: *)
Int[Log[c_.*(b_.*(d_.+e_.*x_)^n_.)^p_.],x_Symbol] :=
(Print["Int(1th)@LogarithmFunctions.m"];
  (d+e*x)*Log[c*(b*(d+e*x)^n)^p]/e - n*p*x) /;
FreeQ[{b,c,d,e,n,p},x]

(* ::Code:: *)
Int[Log[c_.*(a_+b_.*(d_.+e_.*x_)^n_)^p_.],x_Symbol] :=
(Print["Int(2th)@LogarithmFunctions.m"];
  (d+e*x)*Log[c*(a+b*(d+e*x)^n)^p]/e -
  Dist[b*n*p,Int[1/(b+a*(d+e*x)^(-n)),x]]) /;
FreeQ[{a,b,c,d,e,p},x] && RationalQ[n] && n<0

(* ::Code:: *)
Int[Log[c_.*(a_+b_.*(d_.+e_.*x_)^n_.)^p_.],x_Symbol] :=
(Print["Int(3th)@LogarithmFunctions.m"];
  (d+e*x)*Log[c*(a+b*(d+e*x)^n)^p]/e - n*p*x +
  Dist[a*n*p,Int[1/(a+b*(d+e*x)^n),x]]) /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[RationalQ[n] && n<0]

(* ::Code:: *)
Int[1/Log[c_.*(d_.+e_.*x_)],x_Symbol] :=
(Print["Int(4th)@LogarithmFunctions.m"];
  LogIntegral[c*(d+e*x)]/(c*e)) /;
FreeQ[{c,d,e},x]

(* ::Code:: *)
Int[1/(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]),x_Symbol] :=
(Print["Int(5th)@LogarithmFunctions.m"];
  (d+e*x)*ExpIntegralEi[(a+b*Log[c*(d+e*x)^n])/(b*n)]/(b*e*n*E^(a/(b*n))*(c*(d+e*x)^n)^(1/n))) /;
FreeQ[{a,b,c,d,e,n},x]

(* ::Code:: *)
Int[1/Sqrt[a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]],x_Symbol] :=
(Print["Int(6th)@LogarithmFunctions.m"];
  Sqrt[Pi]*Rt[b*n,2]*(d+e*x)*Erfi[Sqrt[a+b*Log[c*(d+e*x)^n]]/Rt[b*n,2]]/
    (b*e*n*E^(a/(b*n))*(c*(d+e*x)^n)^(1/n))) /;
FreeQ[{a,b,c,d,e,n},x] && PosQ[b*n]

(* ::Code:: *)
Int[1/Sqrt[a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.]],x_Symbol] :=
(Print["Int(7th)@LogarithmFunctions.m"];
  Sqrt[Pi]*Rt[-b*n,2]*(d+e*x)*Erf[Sqrt[a+b*Log[c*(d+e*x)^n]]/Rt[-b*n,2]]/
    (b*e*n*E^(a/(b*n))*(c*(d+e*x)^n)^(1/n))) /;
FreeQ[{a,b,c,d,e,n},x] && NegQ[b*n]

(* ::Code:: *)
Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_,x_Symbol] :=
(Print["Int(8th)@LogarithmFunctions.m"];
  (d+e*x)*(a+b*Log[c*(d+e*x)^n])^p/e -
  Dist[b*n*p,Int[(a+b*Log[c*(d+e*x)^n])^(p-1),x]]) /;
FreeQ[{a,b,c,d,e,n},x] && RationalQ[p] && p>0

(* ::Code:: *)
Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_,x_Symbol] :=
(Print["Int(9th)@LogarithmFunctions.m"];
  (d+e*x)*(a+b*Log[c*(d+e*x)^n])^(p+1)/(b*e*n*(p+1)) -
  Dist[1/(b*n*(p+1)),Int[(a+b*Log[c*(d+e*x)^n])^(p+1),x]]) /;
FreeQ[{a,b,c,d,e,n},x] && RationalQ[p] && p<-1

(* ::Code:: *)
Int[(a_.+b_.*Log[c_.*(d_.+e_.*x_)^n_.])^p_,x_Symbol] :=
(Print["Int(10th)@LogarithmFunctions.m"];
  (d+e*x)*Gamma[p+1,-(a+b*Log[c*(d+e*x)^n])/(b*n)]*(a+b*Log[c*(d+e*x)^n])^p/
    (e*(-(a+b*Log[c*(d+e*x)^n])/(b*n))^p*E^(a/(b*n))*(c*(d+e*x)^n)^(1/n))) /;
FreeQ[{a,b,c,d,e,n,p},x] && Not[IntegerQ[2*p]]

(* ::Code:: *)
Int[Log[1+b_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(11th)@LogarithmFunctions.m"];
  -PolyLog[2,-b*x^n]/n) /;
FreeQ[{b,n},x]

(* ::Code:: *)
Int[Log[c_.*(a_+b_.*x_^n_.)]/x_,x_Symbol] :=
(Print["Int(12th)@LogarithmFunctions.m"];
  Log[a*c]*Log[x] +
  Int[Log[1+b*x^n/a]/x,x]) /;
FreeQ[{a,b,c,n},x] && PositiveQ[a*c]

(* ::Code:: *)
Int[Log[c_.*(a_+b_.*x_^n_.)^p_.]/x_,x_Symbol] :=
(Print["Int(13th)@LogarithmFunctions.m"];
  Log[c*(a+b*x^n)^p]*Log[-b*x^n/a]/n -
  Dist[b*p,Int[x^(n-1)*Log[-b*x^n/a]/(a+b*x^n),x]]) /;
FreeQ[{a,b,c,n,p},x]

(* ::Code:: *)
Int[x_^m_.*Log[c_.*(b_.*x_^n_.)^p_.],x_Symbol] :=
(Print["Int(14th)@LogarithmFunctions.m"];
  x^(m+1)*Log[c*(b*x^n)^p]/(m+1) - n*p*x^(m+1)/(m+1)^2) /;
FreeQ[{b,c,m,n,p},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*Log[c_.*(a_+b_.*x_^n_.)^p_.],x_Symbol] :=
(Print["Int(15th)@LogarithmFunctions.m"];
  x^(m+1)*Log[c*(a+b*x^n)^p]/(m+1) -
  Dist[b*n*p/(m+1),Int[x^(m+n)/(a+b*x^n),x]]) /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[m+1] && NonzeroQ[m-n+1]

(* ::Code:: *)
Int[x_^m_./(a_.+b_.*Log[c_.*x_^n_.]),x_Symbol] :=
(Print["Int(16th)@LogarithmFunctions.m"];
  x^(m+1)*ExpIntegralEi[(m+1)*(a+b*Log[c*x^n])/(b*n)]/(b*n*E^(a*(m+1)/(b*n))*(c*x^n)^((m+1)/n))) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_./Sqrt[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
(Print["Int(17th)@LogarithmFunctions.m"];
  Sqrt[Pi]*x^(m+1)*Erfi[Rt[(m+1)/(b*n),2]*Sqrt[a+b*Log[c*x^n]]]/
    (b*n*Rt[(m+1)/(b*n),2]*E^(a*(m+1)/(b*n))*(c*x^n)^((m+1)/n))) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[m+1] && PosQ[(m+1)/(b*n)]

(* ::Code:: *)
Int[x_^m_./Sqrt[a_.+b_.*Log[c_.*x_^n_.]],x_Symbol] :=
(Print["Int(18th)@LogarithmFunctions.m"];
  Sqrt[Pi]*x^(m+1)*Erf[Rt[-(m+1)/(b*n),2]*Sqrt[a+b*Log[c*x^n]]]/
    (b*n*Rt[-(m+1)/(b*n),2]*E^(a*(m+1)/(b*n))*(c*x^n)^((m+1)/n))) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[m+1] && NegQ[(m+1)/(b*n)]

(* ::Code:: *)
Int[x_^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
(Print["Int(19th)@LogarithmFunctions.m"];
  x^(m+1)*(a+b*Log[c*x^n])^p/(m+1) -
  Dist[b*n*p/(m+1),Int[x^m*(a+b*Log[c*x^n])^(p-1),x]]) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[m+1] && RationalQ[p] && p>0

(* ::Code:: *)
Int[x_^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
(Print["Int(20th)@LogarithmFunctions.m"];
  x^(m+1)*(a+b*Log[c*x^n])^(p+1)/(b*n*(p+1)) -
  Dist[(m+1)/(b*n*(p+1)),Int[x^m*(a+b*Log[c*x^n])^(p+1),x]]) /;
FreeQ[{a,b,c,m,n},x] && NonzeroQ[m+1] && RationalQ[p] && p<-1

(* ::Code:: *)
Int[x_^m_.*(a_.+b_.*Log[c_.*x_^n_.])^p_,x_Symbol] :=
(Print["Int(21th)@LogarithmFunctions.m"];
  x^(m+1)*Gamma[p+1,-(m+1)*(a+b*Log[c*x^n])/(b*n)]*(a+b*Log[c*x^n])^p/
    ((m+1)*E^(a*(m+1)/(b*n))*(c*x^n)^((m+1)/n)*(-(m+1)*(a+b*Log[c*x^n])/(b*n))^p)) /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[Log[a_.*(b_.*x_^n_.)^p_]^q_.,x_Symbol] :=
(Print["Int(22th)@LogarithmFunctions.m"];
  Subst[Int[Log[x^(n*p)]^q,x],x^(n*p),a*(b*x^n)^p]) /;
FreeQ[{a,b,n,p,q},x]

(* ::Code:: *)
Int[Log[a_.*(b_.*(c_.*x_^n_.)^p_)^q_]^r_.,x_Symbol] :=
(Print["Int(23th)@LogarithmFunctions.m"];
  Subst[Int[Log[x^(n*p*q)]^r,x],x^(n*p*q),a*(b*(c*x^n)^p)^q]) /;
FreeQ[{a,b,c,n,p,q,r},x]

(* ::Code:: *)
Int[x_^m_.*Log[a_.*(b_.*x_^n_.)^p_]^q_.,x_Symbol] :=
(Print["Int(24th)@LogarithmFunctions.m"];
  Subst[Int[x^m*Log[x^(n*p)]^q,x],x^(n*p),a*(b*x^n)^p]) /;
FreeQ[{a,b,m,n,p,q},x] && NonzeroQ[m+1] && Not[x^(n*p)===a*(b*x^n)^p]

(* ::Code:: *)
Int[x_^m_.*Log[a_.*(b_.*(c_.*x_^n_.)^p_)^q_]^r_.,x_Symbol] :=
(Print["Int(25th)@LogarithmFunctions.m"];
  Subst[Int[x^m*Log[x^(n*p*q)]^r,x],x^(n*p*q),a*(b*(c*x^n)^p)^q]) /;
FreeQ[{a,b,c,m,n,p,q,r},x] && NonzeroQ[m+1] && Not[x^(n*p*q)===a*(b*(c*x^n)^p)^q]

(* ::Code:: *)
Int[x_^m_.*Log[c_.*(a_+b_.*x_)^n_.]^p_,x_Symbol] :=
(Print["Int(26th)@LogarithmFunctions.m"];
  x^m*(a+b*x)*Log[c*(a+b*x)^n]^p/(b*(m+1)) -
  Dist[a*m/(b*(m+1)),Int[x^(m-1)*Log[c*(a+b*x)^n]^p,x]] -
  Dist[n*p/(m+1),Int[x^m*Log[c*(a+b*x)^n]^(p-1),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[{m,p}] && m>0 && p>0

(* ::Code:: *)
Int[Log[c_.*(a_+b_.*x_)^n_.]^p_/x_^2,x_Symbol] :=
(Print["Int(27th)@LogarithmFunctions.m"];
  -(a+b*x)*Log[c*(a+b*x)^n]^p/(a*x) +
  Dist[b*n*p/a,Int[Log[c*(a+b*x)^n]^(p-1)/x,x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>0

(* ::Code:: *)
Int[x_^m_.*Log[c_.*(a_+b_.*x_)^n_.]^p_,x_Symbol] :=
(Print["Int(28th)@LogarithmFunctions.m"];
  x^(m+1)*(a+b*x)*Log[c*(a+b*x)^n]^p/(a*(m+1)) -
  Dist[(b*(m+2))/(a*(m+1)),Int[x^(m+1)*Log[c*(a+b*x)^n]^p,x]] -
  Dist[b*n*p/(a*(m+1)),Int[x^(m+1)*Log[c*(a+b*x)^n]^(p-1),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[{m,p}] && m<-1 && m!=-2 && p>0

(* ::Code:: *)
Int[x_^m_.*Log[c_.*(a_+b_.*x_)^n_.]^p_,x_Symbol] :=
(Print["Int(29th)@LogarithmFunctions.m"];
  Dist[1/b,Subst[Int[(-a/b+x/b)^m*Log[c*x^n]^p,x],x,a+b*x]]) /;
FreeQ[{a,b,c,n,p},x] && IntegerQ[m] && m>0 && Not[RationalQ[p] && p>0]

(* ::Code:: *)
Int[Log[c_.*(a_.+b_.*x_)]/(d_+e_.*x_),x_Symbol] :=
(Print["Int(30th)@LogarithmFunctions.m"];
  -PolyLog[2,1-a*c-b*c*x]/e) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a*c*e-b*c*d-e]

(* ::Code:: *)
Int[Log[c_.*(a_.+b_.*x_)^n_.]/(d_+e_.*x_),x_Symbol] :=
(Print["Int(31th)@LogarithmFunctions.m"];
  Log[c*(a+b*x)^n]*Log[b*(d+e*x)/(b*d-a*e)]/e +
  n*PolyLog[2,-e*(a+b*x)/(b*d-a*e)]/e) /;
FreeQ[{a,b,c,d,e,n},x] && NonzeroQ[b*d-a*e]

(* ::Code:: *)
Int[Log[c_.*(a_+b_.*x_)^n_.]^p_./(d_.+e_.*x_),x_Symbol] :=
(Print["Int(32th)@LogarithmFunctions.m"];
  Log[c*(a+b*x)^n]^p*Log[b*(d+e*x)/(b*d-a*e)]/e -
  Dist[b*n*p/e,Int[Log[c*(a+b*x)^n]^(p-1)*Log[b*(d+e*x)/(b*d-a*e)]/(a+b*x),x]]) /;
FreeQ[{a,b,c,d,e,n},x] && RationalQ[p] && p>0 && NonzeroQ[b*d-a*e]

(* ::Code:: *)
Int[Log[c_.*(a_+b_.*x_)^n_.]^p_.*Log[h_.*(f_.+g_.*x_)]/(d_+e_.*x_),x_Symbol] :=
(Print["Int(33th)@LogarithmFunctions.m"];
  Module[{q=Simplify[1-h*(f+g*x)]},
  -Log[c*(a+b*x)^n]^p*PolyLog[2,q]/e +
  Dist[b*n*p/e,Int[Log[c*(a+b*x)^n]^(p-1)*PolyLog[2,q]/(a+b*x),x]]]) /;
FreeQ[{a,b,c,d,e,f,g,h,n},x] && RationalQ[p] && p>0 && ZeroQ[b*d-a*e] && ZeroQ[a*g*h-b*(f*h-1)]

(* ::Code:: *)
Int[Log[c_.*(a_+b_.*x_)^n_.]^p_.*PolyLog[m_,h_.*(f_.+g_.*x_)]/(d_+e_.*x_),x_Symbol] :=
(Print["Int(34th)@LogarithmFunctions.m"];
  Log[c*(a+b*x)^n]^p*PolyLog[m+1,h*(f+g*x)]/e -
  Dist[b*n*p/e,Int[Log[c*(a+b*x)^n]^(p-1)*PolyLog[m+1,h*(f+g*x)]/(a+b*x),x]]) /;
FreeQ[{a,b,c,d,e,f,g,h,m,n},x] && RationalQ[p] && p>0 && ZeroQ[b*d-a*e] && ZeroQ[a*g-b*f]

(* ::Code:: *)
Int[(d_.+e_.*x_)^m_.*Log[c_.*(a_.+b_.*x_)^n_.]^p_,x_Symbol] :=
(Print["Int(35th)@LogarithmFunctions.m"];
  (d+e*x)^(m+1)*Log[c*(a+b*x)^n]^p/(e*(m+1)) -
  Dist[b*n*p/(e*(m+1)),Int[Regularize[(d+e*x)^(m+1)*Log[c*(a+b*x)^n]^(p-1)/(a+b*x),x],x]]) /;
FreeQ[{a,b,c,d,e,n},x] && IntegersQ[m,p] && m<-1 && p>0

(* ::Code:: *)
Int[Log[c_.*(a_+b_./x_)^n_.]^p_, x_Symbol] :=
(Print["Int(36th)@LogarithmFunctions.m"];
  (b+a*x)*Log[c*(a+b/x)^n]^p/a + 
  Dist[b/a*n*p,Int[Log[c*(a+b/x)^n]^(p-1)/x,x]]) /;
FreeQ[{a,b,c,n},x] && IntegerQ[p] && p>0

(* ::Code:: *)
Int[Log[c_.*(a_+b_.*x_^2)^n_.]^2, x_Symbol] :=
(Print["Int(37th)@LogarithmFunctions.m"];
  x*Log[c*(a+b*x^2)^n]^2 + 
    8*n^2*x -
    4*n*x*Log[c*(a+b*x^2)^n] + 
    (n*Sqrt[a]/Sqrt[-b])*( 
      4*n*Log[(-Sqrt[a]+Sqrt[-b]*x)/(Sqrt[a]+Sqrt[-b]*x)] - 
      4*n*ArcTanh[Sqrt[-b]*x/Sqrt[a]]*(Log[-Sqrt[a]/Sqrt[-b]+x] + Log[Sqrt[a]/Sqrt[-b]+x]) -
      n*Log[-Sqrt[a]/Sqrt[-b]+x]^2 + 
      n*Log[Sqrt[a]/Sqrt[-b]+x]^2 - 
      2*n*Log[Sqrt[a]/Sqrt[-b]+x]*Log[1/2-Sqrt[-b]*x/(2*Sqrt[a])] + 
      2*n*Log[-Sqrt[a]/Sqrt[-b]+x]*Log[(1+Sqrt[-b]*x/Sqrt[a])/2] + 
      4*ArcTanh[Sqrt[-b]*x/Sqrt[a]]*Log[c*(a+b*x^2)^n] + 
      2*n*PolyLog[2,1/2-Sqrt[-b]*x/(2*Sqrt[a])] - 
      2*n*PolyLog[2,(1+Sqrt[-b]*x/Sqrt[a])/2])) /;
FreeQ[{a,b,c,n},x]

(* ::Code:: *)
Int[Log[d_.*(a_.+b_.*x_+c_.*x_^2)^n_.]^2,x_Symbol] :=
(Print["Int(38th)@LogarithmFunctions.m"];
  x*Log[d*(a+b*x+c*x^2)^n]^2 -
  Dist[2*b*n,Int[x*Log[d*(a+b*x+c*x^2)^n]/(a+b*x+c*x^2),x]] - 
  Dist[4*c*n,Int[x^2*Log[d*(a+b*x+c*x^2)^n]/(a+b*x+c*x^2),x]]) /;
FreeQ[{a,b,c,d,n},x]

(* ::Code:: *)
Int[Log[a_.*Log[b_.*x_^n_.]^p_.],x_Symbol] :=
(Print["Int(39th)@LogarithmFunctions.m"];
  x*Log[a*Log[b*x^n]^p] - 
  Dist[n*p,Int[1/Log[b*x^n],x]]) /;
FreeQ[{a,b,n,p},x]

(* ::Code:: *)
Int[Log[a_.*Log[b_.*x_^n_.]^p_.]/x_,x_Symbol] :=
(Print["Int(40th)@LogarithmFunctions.m"];
  Log[b*x^n]*(-p+Log[a*Log[b*x^n]^p])/n) /;
FreeQ[{a,b,n,p},x]

(* ::Code:: *)
Int[x_^m_.*Log[a_.*Log[b_.*x_^n_.]^p_.],x_Symbol] :=
(Print["Int(41th)@LogarithmFunctions.m"];
  x^(m+1)*Log[a*Log[b*x^n]^p]/(m+1) - 
  Dist[n*p/(m+1),Int[x^m/Log[b*x^n],x]]) /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+1]

(* ::Code:: *)
Int[Log[(a_.+b_.*x_)/(c_+d_.*x_)]^m_./x_,x_Symbol] :=
(Print["Int(42th)@LogarithmFunctions.m"];
  Subst[Int[Log[a/c+x/c]^m/x,x],x,(b*c-a*d)*x/(c+d*x)] - 
  Subst[Int[Log[b/d-x/d]^m/x,x],x,(b*c-a*d)/(c+d*x)]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0 && NonzeroQ[b*c-a*d]

(* ::Code:: *)
Int[(A_.+B_.*Log[c_.+d_.*x_])/Sqrt[a_+b_.*Log[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(43th)@LogarithmFunctions.m"];
  Dist[(b*A-a*B)/b,Int[1/Sqrt[a+b*Log[c+d*x]],x]] +
  Dist[B/b,Int[Sqrt[a+b*Log[c+d*x]],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[b*A-a*B]

(* ::Code:: *)
Int[f_^(a_.*Log[u_]),x_Symbol] :=
(Print["Int(44th)@LogarithmFunctions.m"];
  Int[u^(a*Log[f]),x]) /;
FreeQ[{a,f},x]

(* ::Code:: *)
If[ShowSteps,

Int[u_/x_,x_Symbol] :=
(Print["Int(45th)@LogarithmFunctions.m"];
  Module[{lst=FunctionOfLog[u,x]},
  ShowStep["","Int[f[Log[a*x^n]]/x,x]","Subst[Int[f[x],x],x,Log[a*x^n]]/n",Hold[
  Dist[1/lst[[3]],Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]]]] /;
 Not[FalseQ[lst]]]) /;
SimplifyFlag && NonsumQ[u],

Int[u_/x_,x_Symbol] :=
(Print["Int(46th)@LogarithmFunctions.m"];
  Module[{lst=FunctionOfLog[u,x]},
  Dist[1/lst[[3]],Subst[Int[lst[[1]],x],x,Log[lst[[2]]]]] /;
 Not[FalseQ[lst]]]) /;
NonsumQ[u]]

(* ::Code:: *)
Int[1/(a_.*x_+b_.*x_*Log[c_.*x_^n_.]^m_.),x_Symbol] :=
(Print["Int(47th)@LogarithmFunctions.m"];
  Int[1/(x*(a+b*Log[c*x^n]^m)),x]) /;
FreeQ[{a,b,c,m,n},x]

(* ::Code:: *)
Int[Log[1+c_.*f_^(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(48th)@LogarithmFunctions.m"];
  -PolyLog[2,-c*f^(a+b*x)]/(b*Log[f])) /;
FreeQ[{a,b,c,f},x]

(* ::Code:: *)
Int[Log[c_+d_.*f_^(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(49th)@LogarithmFunctions.m"];
  x*Log[c+d*f^(a+b*x)] - x*Log[1+d/c*f^(a+b*x)] +
  Int[Log[1+d/c*f^(a+b*x)],x]) /;
FreeQ[{a,b,c,d,f},x] && NonzeroQ[c-1]

(* ::Code:: *)
Int[x_^m_.*Log[1+c_.*f_^(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(50th)@LogarithmFunctions.m"];
  -x^m*PolyLog[2,-c*f^(a+b*x)]/(b*Log[f]) +
  Dist[m/(b*Log[f]),Int[x^(m-1)*PolyLog[2,-c*f^(a+b*x)],x]]) /;
FreeQ[{a,b,c,f},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Log[c_+d_.*f_^(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(51th)@LogarithmFunctions.m"];
  x^(m+1)*Log[c+d*f^(a+b*x)]/(m+1) - x^(m+1)*Log[1+d/c*f^(a+b*x)]/(m+1) +
  Int[x^m*Log[1+d/c*f^(a+b*x)],x]) /;
FreeQ[{a,b,c,d,f},x] && NonzeroQ[c-1] && RationalQ[m] && m>0

(* ::Code:: *)
Int[Log[u_],x_Symbol] :=
(Print["Int(52th)@LogarithmFunctions.m"];
  x*Log[u] -
  Int[Regularize[x*D[u,x]/u,x],x]) /;
AlgebraicFunctionQ[u,x]

