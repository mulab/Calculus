(* ::Package:: *)

(* ::Code:: *)
Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
(Print["Int(1th)@PolylogarithmFunctions.m"];
  x*PolyLog[n,a*(b*x^p)^q] -
  Dist[p*q,Int[PolyLog[n-1,a*(b*x^p)^q],x]]) /;
FreeQ[{a,b,p,q},x] && RationalQ[n] && n>0

(* ::Code:: *)
Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
(Print["Int(2th)@PolylogarithmFunctions.m"];
  x*PolyLog[n+1,a*(b*x^p)^q]/(p*q) -
  Dist[1/(p*q),Int[PolyLog[n+1,a*(b*x^p)^q],x]]) /;
FreeQ[{a,b,p,q},x] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[PolyLog[n_,a_.*(b_.*x_^p_.)^q_.]/x_,x_Symbol] :=
(Print["Int(3th)@PolylogarithmFunctions.m"];
  PolyLog[n+1,a*(b*x^p)^q]/(p*q)) /;
FreeQ[{a,b,n,p,q},x]

(* ::Code:: *)
Int[x_^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
(Print["Int(4th)@PolylogarithmFunctions.m"];
  x^(m+1)*PolyLog[n,a*(b*x^p)^q]/(m+1) -
  Dist[p*q/(m+1),Int[x^m*PolyLog[n-1,a*(b*x^p)^q],x]]) /;
FreeQ[{a,b,m,p,q},x] && RationalQ[n] && n>0 && NonzeroQ[m+1]

(* ::Code:: *)
Int[x_^m_.*PolyLog[n_,a_.*(b_.*x_^p_.)^q_.],x_Symbol] :=
(Print["Int(5th)@PolylogarithmFunctions.m"];
  x^(m+1)*PolyLog[n+1,a*(b*x^p)^q]/(p*q) -
  Dist[(m+1)/(p*q),Int[x^m*PolyLog[n+1,a*(b*x^p)^q],x]]) /;
FreeQ[{a,b,m,p,q},x] && RationalQ[n] && n<-1 && NonzeroQ[m+1]

(* ::Code:: *)
Int[PolyLog[n_,u_]/(a_+b_.*x_),x_Symbol] :=
(Print["Int(6th)@PolylogarithmFunctions.m"];
  Dist[1/b,Subst[Int[PolyLog[n,Regularize[Subst[u,x,-a/b+x/b],x]]/x,x],x,a+b*x]]) /;
FreeQ[{a,b,n},x]

(* ::Code:: *)
Int[PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
(Print["Int(7th)@PolylogarithmFunctions.m"];
  x*PolyLog[n,c*(a+b*x)^p] -
  Dist[p,Int[PolyLog[n-1,c*(a+b*x)^p],x]] +
  Dist[a*p,Int[PolyLog[n-1,c*(a+b*x)^p]/(a+b*x),x]]) /;
FreeQ[{a,b,c,p},x] && RationalQ[n] && n>0

(* ::Code:: *)
Int[x_^m_.*PolyLog[n_,c_.*(a_.+b_.*x_)^p_.],x_Symbol] :=
(Print["Int(8th)@PolylogarithmFunctions.m"];
  x^(m+1)*PolyLog[n,c*(a+b*x)^p]/(m+1) -
  Dist[b*p/(m+1),Int[x^(m+1)*PolyLog[n-1,c*(a+b*x)^p]/(a+b*x),x]]) /;
FreeQ[{a,b,c,m,p},x] && RationalQ[n] && n>0 && IntegerQ[m] && m>0

(* ::Code:: *)
Int[PolyLog[n_,c_.*f_^(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(9th)@PolylogarithmFunctions.m"];
  PolyLog[n+1,c*f^(a+b*x)]/(b*Log[f])) /;
FreeQ[{a,b,c,n},x]

(* ::Code:: *)
Int[x_^m_.*PolyLog[n_,c_.*f_^(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(10th)@PolylogarithmFunctions.m"];
  x^m*PolyLog[n+1,c*f^(a+b*x)]/(b*Log[f]) -
  Dist[m/(b*Log[f]),Int[x^(m-1)*PolyLog[n+1,c*f^(a+b*x)],x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[Log[a_.*x_^n_.]^p_.*PolyLog[q_,b_.*x_^m_.]/x_,x_Symbol] :=
(Print["Int(11th)@PolylogarithmFunctions.m"];
  Log[a*x^n]^p*PolyLog[q+1,b*x^m]/m -
  Dist[n*p/m,Int[Log[a*x^n]^(p-1)*PolyLog[q+1,b*x^m]/x,x]]) /;
FreeQ[{a,b,m,n,q},x] && RationalQ[p] && p>0
