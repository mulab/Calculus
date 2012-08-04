(* ::Package:: *)

(* ::Code:: *)
Int[x_^m_.*Sec[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@SecantFunctions.m"];
  -2*I*x^m*ArcTan[E^(I*a+I*b*x)]/b +
  Dist[2*I*m/b,Int[x^(m-1)*ArcTan[E^(I*a+I*b*x)],x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*x_],x_Symbol] :=
(Print["Int(2th)@SecantFunctions.m"];
  -2*x^m*ArcTanh[E^(I*a+I*b*x)]/b +
  Dist[2*m/b,Int[x^(m-1)*ArcTanh[E^(I*a+I*b*x)],x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Sec[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(3th)@SecantFunctions.m"];
  x^m*Tan[a+b*x]/b -
  Dist[m/b,Int[x^(m-1)*Tan[a+b*x],x]]) /;
FreeQ[{a,b},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(4th)@SecantFunctions.m"];
  -x^m*Cot[a+b*x]/b +
  Dist[m/b,Int[x^(m-1)*Cot[a+b*x],x]]) /;
FreeQ[{a,b},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[x_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(5th)@SecantFunctions.m"];
  x*Tan[a+b*x]*Sec[a+b*x]^(n-2)/(b*(n-1)) -
  Sec[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  Dist[(n-2)/(n-1),Int[x*Sec[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && n!=2

(* ::Code:: *)
Int[x_*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(6th)@SecantFunctions.m"];
  -x*Cot[a+b*x]*Csc[a+b*x]^(n-2)/(b*(n-1)) -
  Csc[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  Dist[(n-2)/(n-1),Int[x*Csc[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && n!=2

(* ::Code:: *)
Int[x_^m_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(7th)@SecantFunctions.m"];
  x^m*Tan[a+b*x]*Sec[a+b*x]^(n-2)/(b*(n-1)) -
  m*x^(m-1)*Sec[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  Dist[(n-2)/(n-1),Int[x^m*Sec[a+b*x]^(n-2),x]] +
  Dist[m*(m-1)/(b^2*(n-1)*(n-2)),Int[x^(m-2)*Sec[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n>1 && n!=2

(* ::Code:: *)
Int[x_^m_*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(8th)@SecantFunctions.m"];
  -x^m*Cot[a+b*x]*Csc[a+b*x]^(n-2)/(b*(n-1)) -
  m*x^(m-1)*Csc[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  Dist[(n-2)/(n-1),Int[x^m*Csc[a+b*x]^(n-2),x]] +
  Dist[m*(m-1)/(b^2*(n-1)*(n-2)),Int[x^(m-2)*Csc[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n>1 && n!=2

(* ::Code:: *)
Int[x_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(9th)@SecantFunctions.m"];
  Sec[a+b*x]^n/(b^2*n^2) -
  x*Sin[a+b*x]*Sec[a+b*x]^(n+1)/(b*n) +
  Dist[(n+1)/n,Int[x*Sec[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[x_*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(10th)@SecantFunctions.m"];
  Csc[a+b*x]^n/(b^2*n^2) +
  x*Cos[a+b*x]*Csc[a+b*x]^(n+1)/(b*n) +
  Dist[(n+1)/n,Int[x*Csc[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[x_^m_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(11th)@SecantFunctions.m"];
  m*x^(m-1)*Sec[a+b*x]^n/(b^2*n^2) -
  x^m*Sin[a+b*x]*Sec[a+b*x]^(n+1)/(b*n) +
  Dist[(n+1)/n,Int[x^m*Sec[a+b*x]^(n+2),x]] -
  Dist[m*(m-1)/(b^2*n^2),Int[x^(m-2)*Sec[a+b*x]^n,x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1

(* ::Code:: *)
Int[x_^m_*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(12th)@SecantFunctions.m"];
  m*x^(m-1)*Csc[a+b*x]^n/(b^2*n^2) +
  x^m*Cos[a+b*x]*Csc[a+b*x]^(n+1)/(b*n) +
  Dist[(n+1)/n,Int[x^m*Csc[a+b*x]^(n+2),x]] -
  Dist[m*(m-1)/(b^2*n^2),Int[x^(m-2)*Csc[a+b*x]^n,x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1

(* ::Code:: *)
Int[u_.*(a_+b_.*Sec[v_]^2)^m_,x_Symbol] :=
(Print["Int(13th)@SecantFunctions.m"];
  Dist[b^m,Int[u*Tan[v]^(2*m),x]]) /;
FreeQ[{a,b,m},x] && ZeroQ[a+b] && IntegerQ[m]

(* ::Code:: *)
Int[u_.*(a_+b_.*Csc[v_]^2)^m_,x_Symbol] :=
(Print["Int(14th)@SecantFunctions.m"];
  Dist[b^m,Int[u*Cot[v]^(2*m),x]]) /;
FreeQ[{a,b,m},x] && ZeroQ[a+b] && IntegerQ[m]

(* ::Code:: *)
Int[u_.*(a_+b_.*Sec[v_]^2)^m_,x_Symbol] :=
(Print["Int(15th)@SecantFunctions.m"];
  Int[u*(b*Tan[v]^2)^m,x]) /;
FreeQ[{a,b,m},x] && ZeroQ[a+b] && Not[IntegerQ[m]]

(* ::Code:: *)
Int[u_.*(a_+b_.*Csc[v_]^2)^m_,x_Symbol] :=
(Print["Int(16th)@SecantFunctions.m"];
  Int[u*(b*Cot[v]^2)^m,x]) /;
FreeQ[{a,b,m},x] && ZeroQ[a+b] && Not[IntegerQ[m]]

(* ::Code:: *)
Int[(a_+b_.*Sec[v_]^n_)^m_,x_Symbol] :=
(Print["Int(17th)@SecantFunctions.m"];
  Int[(b+a*Cos[v]^n)^m/Cos[v]^(m*n),x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m<0 && n>1

(* ::Code:: *)
Int[(a_+b_.*Csc[v_]^n_)^m_,x_Symbol] :=
(Print["Int(18th)@SecantFunctions.m"];
  Int[(b+a*Sin[v]^n)^m/Sin[v]^(m*n),x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m<0 && n>1

(* ::Code:: *)
(* Int[Cos[v_]^p_.*(a_+b_.*Sec[v_]^n_.)^m_,x_Symbol] :=
(Print["Int(19th)@SecantFunctions.m"];
  Int[Cos[v]^(p-m*n)*(b+a*Cos[v]^n)^m,x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n,p] && m<0 && n>0 *)

(* ::Code:: *)
(* Int[Sin[v_]^p_.*(a_+b_.*Csc[v_]^n_.)^m_,x_Symbol] :=
(Print["Int(20th)@SecantFunctions.m"];
  Int[Sin[v]^(p-m*n)*(b+a*Sin[v]^n)^m,x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n,p] && m<0 && n>0 *)

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]*Sec[a_.+b_.*x_],x_Symbol] :=
(Print["Int(21th)@SecantFunctions.m"];
  Log[Tan[a+b*x]]/b) /;
FreeQ[{a,b},x] && PosQ[b]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(22th)@SecantFunctions.m"];
  Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n-1)/(b*(n-1))) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n-2] && NonzeroQ[n-1] && PosQ[n]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_.*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(23th)@SecantFunctions.m"];
  Dist[1/b,Subst[Int[Regularize[(1+x^2)^((m+n)/2-1)/x^m,x],x],x,Tan[a+b*x]]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && EvenQ[m+n] && 0<m<=n

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(24th)@SecantFunctions.m"];
  Csc[a+b*x]^(m+1)*Sec[a+b*x]^(n-1)/(b*(n-1)) +
  Dist[(m+1)/(n-1),Int[Csc[a+b*x]^(m+2)*Sec[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m<-1 && n>1

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_.*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(25th)@SecantFunctions.m"];
  Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n-1)/(b*(n-1)) +
  Dist[(m+n-2)/(n-1),Int[Csc[a+b*x]^m*Sec[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && Not[EvenQ[m+n]] && Not[EvenQ[n] && OddQ[m] && m>1]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_.*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(26th)@SecantFunctions.m"];
  -Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n+1)/(b*(m+n)) +
  Dist[(n+1)/(m+n),Int[Csc[a+b*x]^m*Sec[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]*Sec[a_.+b_.*x_],x_Symbol] :=
(Print["Int(27th)@SecantFunctions.m"];
  -Log[Cot[a+b*x]]/b) /;
FreeQ[{a,b},x] && NegQ[b]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(28th)@SecantFunctions.m"];
  -Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n-1)/(b*(m-1))) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n-2] && NonzeroQ[m-1] && PosQ[m]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Sec[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(29th)@SecantFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[(1+x^2)^((m+n)/2-1)/x^n,x],x],x,Cot[a+b*x]]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && EvenQ[m+n] && 0<n<m

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(30th)@SecantFunctions.m"];
  -Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n+1)/(b*(m-1)) +
  Dist[(n+1)/(m-1),Int[Csc[a+b*x]^(m-2)*Sec[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Sec[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(31th)@SecantFunctions.m"];
  -Csc[a+b*x]^(m-1)*Sec[a+b*x]^(n-1)/(b*(m-1)) +
  Dist[(m+n-2)/(m-1),Int[Csc[a+b*x]^(m-2)*Sec[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && Not[EvenQ[m+n]] && Not[EvenQ[m] && OddQ[n] && n>1]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Sec[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(32th)@SecantFunctions.m"];
  Csc[a+b*x]^(m+1)*Sec[a+b*x]^(n-1)/(b*(m+n)) +
  Dist[(m+1)/(m+n),Int[Csc[a+b*x]^(m+2)*Sec[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n]

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_.*Tan[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(33th)@SecantFunctions.m"];
  Sec[a+b*x]^m/(b*m)) /;
FreeQ[{a,b,m},x] && n===1

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_.*Cot[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(34th)@SecantFunctions.m"];
  -Csc[a+b*x]^m/(b*m)) /;
FreeQ[{a,b,m},x] && n===1

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(35th)@SecantFunctions.m"];
  Dist[1/b,Subst[Int[Regularize[x^n*(1+x^2)^((m-2)/2),x],x],x,Tan[a+b*x]]]) /;
FreeQ[{a,b,n},x] && EvenQ[m] && m>2 && Not[OddQ[n] && 0<n<m-1]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(36th)@SecantFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[x^n*(1+x^2)^((m-2)/2),x],x],x,Cot[a+b*x]]]) /;
FreeQ[{a,b,n},x] && EvenQ[m] && m>2 && Not[OddQ[n] && 0<n<m-1]

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_.*Tan[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(37th)@SecantFunctions.m"];
  Dist[1/b,Subst[Int[Regularize[x^(m-1)*(-1+x^2)^((n-1)/2),x],x],x,Sec[a+b*x]]]) /;
FreeQ[{a,b,m},x] && OddQ[n] && Not[EvenQ[m] && 0<m<=n+1]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_.*Cot[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(38th)@SecantFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[x^(m-1)*(-1+x^2)^((n-1)/2),x],x],x,Csc[a+b*x]]]) /;
FreeQ[{a,b,m},x] && OddQ[n] && Not[EvenQ[m] && 0<m<=n+1]

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(39th)@SecantFunctions.m"];
  Sec[a+b*x]^(m-2)*Tan[a+b*x]^(n+1)/(b*(n+1)) -
  Dist[(m-2)/(n+1),Int[Sec[a+b*x]^(m-2)*Tan[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(40th)@SecantFunctions.m"];
  -Csc[a+b*x]^(m-2)*Cot[a+b*x]^(n+1)/(b*(n+1)) -
  Dist[(m-2)/(n+1),Int[Csc[a+b*x]^(m-2)*Cot[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(41th)@SecantFunctions.m"];
  Sec[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*m) -
  Dist[(n-1)/m,Int[Sec[a+b*x]^(m+2)*Tan[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m<-1 && n>1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(42th)@SecantFunctions.m"];
  -Csc[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*m) -
  Dist[(n-1)/m,Int[Csc[a+b*x]^(m+2)*Cot[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m<-1 && n>1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(43th)@SecantFunctions.m"];
  -Sec[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*m)) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n+1]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_.*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(44th)@SecantFunctions.m"];
  Csc[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*m)) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n+1]

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(45th)@SecantFunctions.m"];
  -Sec[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*m) +
  Dist[(m+n+1)/m,Int[Sec[a+b*x]^(m+2)*Tan[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(46th)@SecantFunctions.m"];
  Csc[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*m) +
  Dist[(m+n+1)/m,Int[Csc[a+b*x]^(m+2)*Cot[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(47th)@SecantFunctions.m"];
  Sec[a+b*x]^(m-2)*Tan[a+b*x]^(n+1)/(b*(m+n-1)) +
  Dist[(m-2)/(m+n-1),Int[Sec[a+b*x]^(m-2)*Tan[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && Not[EvenQ[m]] && Not[OddQ[n]]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(48th)@SecantFunctions.m"];
  -Csc[a+b*x]^(m-2)*Cot[a+b*x]^(n+1)/(b*(m+n-1)) +
  Dist[(m-2)/(m+n-1),Int[Csc[a+b*x]^(m-2)*Cot[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && Not[EvenQ[m]] && Not[OddQ[n]]

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_.*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(49th)@SecantFunctions.m"];
  Sec[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*(m+n-1)) -
  Dist[(n-1)/(m+n-1),Int[Sec[a+b*x]^m*Tan[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1] && Not[EvenQ[m]] && Not[OddQ[n]]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_.*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(50th)@SecantFunctions.m"];
  -Csc[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*(m+n-1)) -
  Dist[(n-1)/(m+n-1),Int[Csc[a+b*x]^m*Cot[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1] && Not[EvenQ[m]] && Not[OddQ[n]]

(* ::Code:: *)
Int[Sec[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(51th)@SecantFunctions.m"];
  Sec[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*(n+1)) -
  Dist[(m+n+1)/(n+1),Int[Sec[a+b*x]^m*Tan[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Csc[a_.+b_.*x_]^m_.*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(52th)@SecantFunctions.m"];
  -Csc[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*(n+1)) -
  Dist[(m+n+1)/(n+1),Int[Csc[a+b*x]^m*Cot[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[x_^m_.*Sec[a_.+b_.*x_^n_.]^p_*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(53th)@SecantFunctions.m"];
  x^(m-n+1)*Sec[a+b*x^n]^(p-1)/(b*n*(p-1)) -
  Dist[(m-n+1)/(b*n*(p-1)),Int[x^(m-n)*Sec[a+b*x^n]^(p-1),x]]) /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*x_^n_.]^p_*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(54th)@SecantFunctions.m"];
  -x^(m-n+1)*Csc[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  Dist[(m-n+1)/(b*n*(p-1)),Int[x^(m-n)*Csc[a+b*x^n]^(p-1),x]]) /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]

(* ::Code:: *)
Int[x_^m_.*Sec[a_.+b_.*x_^n_.]^p_.*Tan[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
(Print["Int(55th)@SecantFunctions.m"];
  x^(m-n+1)*Sec[a+b*x^n]^p/(b*n*p) -
  Dist[(m-n+1)/(b*n*p),Int[x^(m-n)*Sec[a+b*x^n]^p,x]]) /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*x_^n_.]^p_.*Cot[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
(Print["Int(56th)@SecantFunctions.m"];
  -x^(m-n+1)*Csc[a+b*x^n]^p/(b*n*p) +
  Dist[(m-n+1)/(b*n*p),Int[x^(m-n)*Csc[a+b*x^n]^p,x]]) /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1

(* ::Code:: *)
Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(57th)@SecantFunctions.m"];
  x*(b*n*(p-2)+Tan[a+b*Log[c*x^n]])*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1))) /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[p-1] && ZeroQ[b^2*n^2*(p-2)^2+1]

(* ::Code:: *)
Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(58th)@SecantFunctions.m"];
  x*(b*n*(p-2)-Cot[a+b*Log[c*x^n]])*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1))) /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[p-1] && ZeroQ[b^2*n^2*(p-2)^2+1]

(* ::Code:: *)
Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(59th)@SecantFunctions.m"];
  x*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  x*Sec[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  Dist[(b^2*n^2*(p-2)^2+1)/(b^2*n^2*(p-1)*(p-2)),Int[Sec[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2+1]

(* ::Code:: *)
Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(60th)@SecantFunctions.m"];
  -x*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  x*Csc[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  Dist[(b^2*n^2*(p-2)^2+1)/(b^2*n^2*(p-1)*(p-2)),Int[Csc[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2+1]

(* ::Code:: *)
Int[Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(61th)@SecantFunctions.m"];
  -b*n*p*x*Sin[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+1) +
  x*Sec[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) +
  Dist[b^2*n^2*p*(p+1)/(b^2*n^2*p^2+1),Int[Sec[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2+1]

(* ::Code:: *)
Int[Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(62th)@SecantFunctions.m"];
  b*n*p*x*Cos[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+1) +
  x*Csc[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+1) +
  Dist[b^2*n^2*p*(p+1)/(b^2*n^2*p^2+1),Int[Csc[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2+1]

(* ::Code:: *)
Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(63th)@SecantFunctions.m"];
  x^(m+1)*(b*n*(p-2)+(m+1)*Tan[a+b*Log[c*x^n]])*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(m+1)*(p-1))) /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[m+1] && NonzeroQ[p-1] && ZeroQ[b^2*n^2*(p-2)^2+(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(64th)@SecantFunctions.m"];
  x^(m+1)*(b*n*(p-2)-(m+1)*Cot[a+b*Log[c*x^n]])*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(m+1)*(p-1))) /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[m+1] && NonzeroQ[p-1] && ZeroQ[b^2*n^2*(p-2)^2+(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(65th)@SecantFunctions.m"];
  x^(m+1)*Tan[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  (m+1)*x^(m+1)*Sec[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  Dist[(b^2*n^2*(p-2)^2+(m+1)^2)/(b^2*n^2*(p-1)*(p-2)),Int[x^m*Sec[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2+(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(66th)@SecantFunctions.m"];
  -x^(m+1)*Cot[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  (m+1)*x^(m+1)*Csc[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  Dist[(b^2*n^2*(p-2)^2+(m+1)^2)/(b^2*n^2*(p-1)*(p-2)),Int[x^m*Csc[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2+(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(67th)@SecantFunctions.m"];
  -b*n*p*x^(m+1)*Sin[a+b*Log[c*x^n]]*Sec[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+(m+1)^2) +
  (m+1)*x^(m+1)*Sec[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) +
  Dist[b^2*n^2*p*(p+1)/(b^2*n^2*p^2+(m+1)^2),Int[x^m*Sec[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2+(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(68th)@SecantFunctions.m"];
  b*n*p*x^(m+1)*Cos[a+b*Log[c*x^n]]*Csc[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2+(m+1)^2) +
  (m+1)*x^(m+1)*Csc[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2+(m+1)^2) +
  Dist[b^2*n^2*p*(p+1)/(b^2*n^2*p^2+(m+1)^2),Int[x^m*Csc[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2+(m+1)^2]

(* ::Code:: *)
Int[u_*Csc[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(69th)@SecantFunctions.m"];
  Dist[1/2^n,Int[u*Csc[a/2+b*x/2]^n*Sec[a/2+b*x/2]^n,x]]) /;
FreeQ[{a,b},x] && IntegerQ[n] && ZeroQ[a/2+b*x/2-FunctionOfTrig[u,x]]

(* ::Code:: *)
(* Int[u_*Csc[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(70th)@SecantFunctions.m"];
  Csc[a+b*x]^n/(Csc[a/2+b*x/2]^n*Sec[a/2+b*x/2]^n)*Int[u*Csc[a/2+b*x/2]^n*Sec[a/2+b*x/2]^n,x]) /;
FreeQ[{a,b},x] && FractionQ[n] && ZeroQ[a/2+b*x/2-FunctionOfTrig[u,x]] *)

