(* ::Package:: *)

(* ::Code:: *)
Int[Sech[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@HyperbolicSecantFunctions.m"];

  ArcTan[Sinh[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_],x_Symbol] :=
(Print["Int(2th)@HyperbolicSecantFunctions.m"];

  -ArcCoth[Cosh[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(3th)@HyperbolicSecantFunctions.m"];
  Tanh[a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(4th)@HyperbolicSecantFunctions.m"];
  -Coth[a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(5th)@HyperbolicSecantFunctions.m"];
  Dist[1/b,Subst[Int[Regularize[(1-x^2)^((n-2)/2),x],x],x,Tanh[a+b*x]]]) /;
FreeQ[{a,b},x] && EvenQ[n] && n>1

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(6th)@HyperbolicSecantFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[(-1+x^2)^((n-2)/2),x],x],x,Coth[a+b*x]]]) /;
FreeQ[{a,b},x] && EvenQ[n] && n>1

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(7th)@HyperbolicSecantFunctions.m"];
  Sinh[a+b*x]*Sech[a+b*x]^(n-1)/(b*(n-1)) + 
  Dist[(n-2)/(n-1),Int[Sech[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && Not[EvenQ[n]] && RationalQ[n] && n>1

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(8th)@HyperbolicSecantFunctions.m"];
  -Cosh[a+b*x]*Csch[a+b*x]^(n-1)/(b*(n-1)) - 
  Dist[(n-2)/(n-1),Int[Csch[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && Not[EvenQ[n]] && RationalQ[n] && n>1

(* ::Code:: *)
Int[1/Sqrt[Sech[a_.+b_.*x_]],x_Symbol] :=
(Print["Int(9th)@HyperbolicSecantFunctions.m"];
  Sqrt[Cosh[a+b*x]]*Sqrt[Sech[a+b*x]]*Int[Sqrt[Cosh[a+b*x]],x]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[(c_.*Sech[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(10th)@HyperbolicSecantFunctions.m"];
  (c*Sech[a+b*x])^n*Cosh[a+b*x]^n*Int[1/Cosh[a+b*x]^n,x]) /;
FreeQ[{a,b,c},x] && RationalQ[n] && -1<n<1

(* ::Code:: *)
Int[1/Sqrt[Csch[a_.+b_.*x_]],x_Symbol] :=
(Print["Int(11th)@HyperbolicSecantFunctions.m"];
  Sqrt[Csch[a+b*x]]*Sqrt[Sinh[a+b*x]]*Int[Sqrt[Sinh[a+b*x]],x]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[(c_.*Csch[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(12th)@HyperbolicSecantFunctions.m"];
  (c*Csch[a+b*x])^n*Sinh[a+b*x]^n*Int[1/Sinh[a+b*x]^n,x]) /;
FreeQ[{a,b,c},x] && RationalQ[n] && -1<n<1

(* ::Code:: *)
Int[(c_.*Sech[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(13th)@HyperbolicSecantFunctions.m"];
  c*Sinh[a+b*x]*(c*Sech[a+b*x])^(n-1)/(b*(n-1)) + 
  Dist[c^2*(n-2)/(n-1),Int[(c*Sech[a+b*x])^(n-2),x]]) /;
FreeQ[{a,b,c},x] && FractionQ[n] && n>1

(* ::Code:: *)
Int[(c_.*Csch[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(14th)@HyperbolicSecantFunctions.m"];
  -c*Cosh[a+b*x]*(c*Csch[a+b*x])^(n-1)/(b*(n-1)) - 
  Dist[c^2*(n-2)/(n-1),Int[(c*Csch[a+b*x])^(n-2),x]]) /;
FreeQ[{a,b,c},x] && FractionQ[n] && n>1

(* ::Code:: *)
Int[(c_.*Sech[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(15th)@HyperbolicSecantFunctions.m"];
  -Sinh[a+b*x]*(c*Sech[a+b*x])^(n+1)/(b*c*n) + 
  Dist[(n+1)/(c^2*n),Int[(c*Sech[a+b*x])^(n+2),x]]) /;
FreeQ[{a,b,c},x] && FractionQ[n] && n<-1

(* ::Code:: *)
Int[(c_.*Csch[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(16th)@HyperbolicSecantFunctions.m"];
  -Cosh[a+b*x]*(c*Csch[a+b*x])^(n+1)/(b*c*n) - 
  Dist[(n+1)/(c^2*n),Int[(c*Csch[a+b*x])^(n+2),x]]) /;
FreeQ[{a,b,c},x] && FractionQ[n] && n<-1

(* ::Code:: *)
Int[Sqrt[a_+b_.*Sech[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(17th)@HyperbolicSecantFunctions.m"];
  2*a*ArcTan[Sqrt[-1+a/b*Sech[c+d*x]]]*Tanh[c+d*x]/
		(d*Sqrt[-1+a/b*Sech[c+d*x]]*Sqrt[a+b*Sech[c+d*x]])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

(* ::Code:: *)
Int[Sqrt[a_+b_.*Csch[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(18th)@HyperbolicSecantFunctions.m"];
  2*a*ArcTan[Sqrt[-1-a/b*Csch[c+d*x]]]*Coth[c+d*x]/
		(d*Sqrt[-1-a/b*Csch[c+d*x]]*Sqrt[a+b*Csch[c+d*x]])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*Sech[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(19th)@HyperbolicSecantFunctions.m"];
  -Coth[c+d*x]*Sqrt[-a+b*Sech[c+d*x]]*Sqrt[a+b*Sech[c+d*x]]/(a^(3/2)*d)*
    (Sqrt[2]*ArcTan[Sqrt[2*a]/Sqrt[-a+b*Sech[c+d*x]]]+2*ArcTan[Sqrt[-a+b*Sech[c+d*x]]/Sqrt[a]])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*Csch[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(20th)@HyperbolicSecantFunctions.m"];
  -Sqrt[-a+b*Csch[c+d*x]]*Sqrt[a+b*Csch[c+d*x]]*Tanh[c+d*x]/a^(3/2)*
    (Sqrt[2]*ArcTan[Sqrt[2*a]/Sqrt[-a+b*Csch[c+d*x]]]+2*ArcTan[Sqrt[-a+b*Csch[c+d*x]]/Sqrt[a]])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]

(* ::Code:: *)
Int[x_^m_.*Sech[a_.+b_.*x_],x_Symbol] :=
(Print["Int(21th)@HyperbolicSecantFunctions.m"];
  2*x^m*ArcTan[E^(a+b*x)]/b -
  Dist[2*m/b,Int[x^(m-1)*ArcTan[E^(a+b*x)],x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Csch[a_.+b_.*x_],x_Symbol] :=
(Print["Int(22th)@HyperbolicSecantFunctions.m"];
  -2*x^m*ArcTanh[E^(a+b x)]/b +
  Dist[2*m/b,Int[x^(m-1)*ArcTanh[E^(a+b x)],x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Sech[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(23th)@HyperbolicSecantFunctions.m"];
  x^m*Tanh[a+b*x]/b -
  Dist[m/b,Int[x^(m-1)*Tanh[a+b*x],x]]) /;
FreeQ[{a,b},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[x_^m_.*Csch[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(24th)@HyperbolicSecantFunctions.m"];
  -x^m*Coth[a+b*x]/b +
  Dist[m/b,Int[x^(m-1)*Coth[a+b*x],x]]) /;
FreeQ[{a,b},x] && RationalQ[m] && m>0

(* ::Code:: *)
Int[x_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(25th)@HyperbolicSecantFunctions.m"];
  x*Tanh[a+b*x]*Sech[a+b*x]^(n-2)/(b*(n-1)) +
  Sech[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  Dist[(n-2)/(n-1),Int[x*Sech[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && n!=2

(* ::Code:: *)
Int[x_*Csch[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(26th)@HyperbolicSecantFunctions.m"];
  -x*Coth[a+b*x]*Csch[a+b*x]^(n-2)/(b*(n-1)) -
  Csch[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) -
  Dist[(n-2)/(n-1),Int[x*Csch[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n>1 && n!=2

(* ::Code:: *)
Int[x_^m_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(27th)@HyperbolicSecantFunctions.m"];
  x^m*Tanh[a+b*x]*Sech[a+b*x]^(n-2)/(b*(n-1)) +
  m*x^(m-1)*Sech[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) +
  Dist[(n-2)/(n-1),Int[x^m*Sech[a+b*x]^(n-2),x]] -
  Dist[m*(m-1)/(b^2*(n-1)*(n-2)),Int[x^(m-2)*Sech[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n>1 && n!=2

(* ::Code:: *)
Int[x_^m_*Csch[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(28th)@HyperbolicSecantFunctions.m"];
  -x^m*Coth[a+b*x]*Csch[a+b*x]^(n-2)/(b*(n-1)) -
  m*x^(m-1)*Csch[a+b*x]^(n-2)/(b^2*(n-1)*(n-2)) -
  Dist[(n-2)/(n-1),Int[x^m*Csch[a+b*x]^(n-2),x]] +
  Dist[m*(m-1)/(b^2*(n-1)*(n-2)),Int[x^(m-2)*Csch[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n>1 && n!=2

(* ::Code:: *)
Int[x_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(29th)@HyperbolicSecantFunctions.m"];
  -Sech[a+b*x]^n/(b^2*n^2) -
  x*Sinh[a+b*x]*Sech[a+b*x]^(n+1)/(b*n) +
  Dist[(n+1)/n,Int[x*Sech[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[x_*Csch[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(30th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^n/(b^2*n^2) -
  x*Cosh[a+b*x]*Csch[a+b*x]^(n+1)/(b*n) -
  Dist[(n+1)/n,Int[x*Csch[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[x_^m_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(31th)@HyperbolicSecantFunctions.m"];
  -m*x^(m-1)*Sech[a+b*x]^n/(b^2*n^2) -
  x^m*Sinh[a+b*x]*Sech[a+b*x]^(n+1)/(b*n) +
  Dist[(n+1)/n,Int[x^m*Sech[a+b*x]^(n+2),x]] +
  Dist[m*(m-1)/(b^2*n^2),Int[x^(m-2)*Sech[a+b*x]^n,x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1

(* ::Code:: *)
Int[x_^m_*Csch[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(32th)@HyperbolicSecantFunctions.m"];
  -m*x^(m-1)*Csch[a+b*x]^n/(b^2*n^2) -
  x^m*Cosh[a+b*x]*Csch[a+b*x]^(n+1)/(b*n) -
  Dist[(n+1)/n,Int[x^m*Csch[a+b*x]^(n+2),x]] +
  Dist[m*(m-1)/(b^2*n^2),Int[x^(m-2)*Csch[a+b*x]^n,x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1

(* ::Code:: *)
Int[(a_+b_.*Sech[v_]^n_.)^m_,x_Symbol] :=
(Print["Int(33th)@HyperbolicSecantFunctions.m"];
  Int[(b+a*Cosh[v]^n)^m/Cosh[v]^(m*n),x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m<0 && n>0

(* ::Code:: *)
Int[(a_+b_.*Csch[v_]^n_.)^m_,x_Symbol] :=
(Print["Int(34th)@HyperbolicSecantFunctions.m"];
  Int[(b+a*Sinh[v]^n)^m/Sinh[v]^(m*n),x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m<0 && n>0

(* ::Code:: *)
Int[Cosh[v_]^p_.*(a_+b_.*Sech[v_]^n_.)^m_,x_Symbol] :=
(Print["Int(35th)@HyperbolicSecantFunctions.m"];
  Int[Cosh[v]^(p-m*n)*(b+a*Cosh[v]^n)^m,x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n,p] && m<0 && n>0

(* ::Code:: *)
Int[Sinh[v_]^p_.*(a_+b_.*Csch[v_]^n_.)^m_,x_Symbol] :=
(Print["Int(36th)@HyperbolicSecantFunctions.m"];
  Int[Sinh[v]^(p-m*n)*(b+a*Sinh[v]^n)^m,x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n,p] && m<0 && n>0

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]*Sech[a_.+b_.*x_],x_Symbol] :=
(Print["Int(37th)@HyperbolicSecantFunctions.m"];
  Log[Tanh[a+b*x]]/b) /;
FreeQ[{a,b},x] && PosQ[b]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(38th)@HyperbolicSecantFunctions.m"];
  Csch[a+b*x]^(m-1)*Sech[a+b*x]^(n-1)/(b*(n-1))) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n-2] && NonzeroQ[n-1] && PosQ[n]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_.*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(39th)@HyperbolicSecantFunctions.m"];
  Dist[1/b,Subst[Int[Regularize[(1-x^2)^((m+n)/2-1)/x^m,x],x],x,Tanh[a+b*x]]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && EvenQ[m+n] && 0<m<=n

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(40th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^(m+1)*Sech[a+b*x]^(n-1)/(b*(n-1)) -
  Dist[(m+1)/(n-1),Int[Csch[a+b*x]^(m+2)*Sech[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m<-1 && n>1

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_.*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(41th)@HyperbolicSecantFunctions.m"];
  Csch[a+b*x]^(m-1)*Sech[a+b*x]^(n-1)/(b*(n-1)) +
  Dist[(m+n-2)/(n-1),Int[Csch[a+b*x]^m*Sech[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && Not[EvenQ[m+n]] && Not[EvenQ[n] && OddQ[m] && m>1]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_.*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(42th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^(m-1)*Sech[a+b*x]^(n+1)/(b*(m+n)) +
  Dist[(n+1)/(m+n),Int[Csch[a+b*x]^m*Sech[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]*Sech[a_.+b_.*x_],x_Symbol] :=
(Print["Int(43th)@HyperbolicSecantFunctions.m"];
  -Log[Coth[a+b*x]]/b) /;
FreeQ[{a,b},x] && NegQ[b]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(44th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^(m-1)*Sech[a+b*x]^(n-1)/(b*(m-1))) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n-2] && NonzeroQ[m-1] && PosQ[m]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Sech[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(45th)@HyperbolicSecantFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[(-1+x^2)^((m+n)/2-1)/x^n,x],x],x,Coth[a+b*x]]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && EvenQ[m+n] && 0<n<m

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Sech[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(46th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^(m-1)*Sech[a+b*x]^(n+1)/(b*(m-1)) -
  Dist[(n+1)/(m-1),Int[Csch[a+b*x]^(m-2)*Sech[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Sech[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(47th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^(m-1)*Sech[a+b*x]^(n-1)/(b*(m-1)) -
  Dist[(m+n-2)/(m-1),Int[Csch[a+b*x]^(m-2)*Sech[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && Not[EvenQ[m+n]] && Not[EvenQ[m] && OddQ[n] && n>1]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Sech[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(48th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^(m+1)*Sech[a+b*x]^(n-1)/(b*(m+n)) -
  Dist[(m+1)/(m+n),Int[Csch[a+b*x]^(m+2)*Sech[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^m_.*Tanh[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(49th)@HyperbolicSecantFunctions.m"];
  -Sech[a+b*x]^m/(b*m)) /;
FreeQ[{a,b,m},x] && n===1

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_.*Coth[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(50th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^m/(b*m)) /;
FreeQ[{a,b,m},x] && n===1

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^m_*Tanh[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(51th)@HyperbolicSecantFunctions.m"];
  Dist[1/b,Subst[Int[Regularize[x^n*(1-x^2)^((m-2)/2),x],x],x,Tanh[a+b*x]]]) /;
FreeQ[{a,b,n},x] && EvenQ[m] && m>2 && Not[OddQ[n] && 0<n<m-1]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Coth[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(52th)@HyperbolicSecantFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[x^n*(-1+x^2)^((m-2)/2),x],x],x,Coth[a+b*x]]]) /;
FreeQ[{a,b,n},x] && EvenQ[m] && m>2 && Not[OddQ[n] && 0<n<m-1]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^m_.*Tanh[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(53th)@HyperbolicSecantFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[x^(m-1)*(1-x^2)^((n-1)/2),x],x],x,Sech[a+b*x]]]) /;
FreeQ[{a,b,m},x] && OddQ[n] && Not[EvenQ[m] && 0<m<=n+1]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_.*Coth[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(54th)@HyperbolicSecantFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[x^(m-1)*(1+x^2)^((n-1)/2),x],x],x,Csch[a+b*x]]]) /;
FreeQ[{a,b,m},x] && OddQ[n] && Not[EvenQ[m] && 0<m<=n+1]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^m_*Tanh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(55th)@HyperbolicSecantFunctions.m"];
  Sech[a+b*x]^(m-2)*Tanh[a+b*x]^(n+1)/(b*(n+1)) +
  Dist[(m-2)/(n+1),Int[Sech[a+b*x]^(m-2)*Tanh[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_.*Coth[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(56th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^(m-2)*Coth[a+b*x]^(n+1)/(b*(n+1)) -
  Dist[(m-2)/(n+1),Int[Csch[a+b*x]^(m-2)*Coth[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^m_*Tanh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(57th)@HyperbolicSecantFunctions.m"];
  -Sech[a+b*x]^m*Tanh[a+b*x]^(n-1)/(b*m) +
  Dist[(n-1)/m,Int[Sech[a+b*x]^(m+2)*Tanh[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m<-1 && n>1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Coth[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(58th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^m*Coth[a+b*x]^(n-1)/(b*m) -
  Dist[(n-1)/m,Int[Csch[a+b*x]^(m+2)*Coth[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m<-1 && n>1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^m_*Tanh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(59th)@HyperbolicSecantFunctions.m"];
  -Sech[a+b*x]^m*Tanh[a+b*x]^(n+1)/(b*m)) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n+1]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_.*Coth[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(60th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^m*Coth[a+b*x]^(n+1)/(b*m)) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n+1]

(* ::Code:: *)
Inth[Sech[a_.+b_.*x_]^m_*Tanh[a_.+b_.*x_]^n_,x_Symbol] :=
  -Sech[a+b*x]^m*Tanh[a+b*x]^(n+1)/(b*m) +
  Dist[(m+n+1)/m,Int[Sech[a+b*x]^(m+2)*Tanh[a+b*x]^n,x]] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Coth[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(61th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^m*Coth[a+b*x]^(n+1)/(b*m) -
  Dist[(m+n+1)/m,Int[Csch[a+b*x]^(m+2)*Coth[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^m_*Tanh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(62th)@HyperbolicSecantFunctions.m"];
  Sech[a+b*x]^(m-2)*Tanh[a+b*x]^(n+1)/(b*(m+n-1)) +
  Dist[(m-2)/(m+n-1),Int[Sech[a+b*x]^(m-2)*Tanh[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && Not[EvenQ[m]] && Not[OddQ[n]]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_*Coth[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(63th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^(m-2)*Coth[a+b*x]^(n+1)/(b*(m+n-1)) -
  Dist[(m-2)/(m+n-1),Int[Csch[a+b*x]^(m-2)*Coth[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n-1] && Not[EvenQ[m]] && Not[OddQ[n]]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^m_.*Tanh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(64th)@HyperbolicSecantFunctions.m"];
  -Sech[a+b*x]^m*Tanh[a+b*x]^(n-1)/(b*(m+n-1)) +
  Dist[(n-1)/(m+n-1),Int[Sech[a+b*x]^m*Tanh[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1] && Not[EvenQ[m]] && Not[OddQ[n]]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_.*Coth[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(65th)@HyperbolicSecantFunctions.m"];
  -Csch[a+b*x]^m*Coth[a+b*x]^(n-1)/(b*(m+n-1)) +
  Dist[(n-1)/(m+n-1),Int[Csch[a+b*x]^m*Coth[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n-1] && Not[EvenQ[m]] && Not[OddQ[n]]

(* ::Code:: *)
Int[Sech[a_.+b_.*x_]^m_*Tanh[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(66th)@HyperbolicSecantFunctions.m"];
  Sech[a+b*x]^m*Tanh[a+b*x]^(n+1)/(b*(n+1)) +
  Dist[(m+n+1)/(n+1),Int[Sech[a+b*x]^m*Tanh[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[Csch[a_.+b_.*x_]^m_.*Coth[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(67th)@HyperbolicSecantFunctions.m"];
  Csch[a+b*x]^m*Coth[a+b*x]^(n+1)/(b*(n+1)) +
  Dist[(m+n+1)/(n+1),Int[Csch[a+b*x]^m*Coth[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && Not[EvenQ[m]]

(* ::Code:: *)
Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_*Sinh[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(68th)@HyperbolicSecantFunctions.m"];
  -x^(m-n+1)*Sech[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  Dist[(m-n+1)/(b*n*(p-1)),Int[x^(m-n)*Sech[a+b*x^n]^(p-1),x]]) /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]

(* ::Code:: *)
Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_*Cosh[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(69th)@HyperbolicSecantFunctions.m"];
  -x^(m-n+1)*Csch[a+b*x^n]^(p-1)/(b*n*(p-1)) +
  Dist[(m-n+1)/(b*n*(p-1)),Int[x^(m-n)*Csch[a+b*x^n]^(p-1),x]]) /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && NonzeroQ[p-1]

(* ::Code:: *)
Int[x_^m_.*Sech[a_.+b_.*x_^n_.]^p_.*Tanh[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
(Print["Int(70th)@HyperbolicSecantFunctions.m"];
  -x^(m-n+1)*Sech[a+b*x^n]^p/(b*n*p) +
  Dist[(m-n+1)/(b*n*p),Int[x^(m-n)*Sech[a+b*x^n]^p,x]]) /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1

(* ::Code:: *)
Int[x_^m_.*Csch[a_.+b_.*x_^n_.]^p_.*Coth[a_.+b_.*x_^n_.]^q_.,x_Symbol] :=
(Print["Int(71th)@HyperbolicSecantFunctions.m"];
  -x^(m-n+1)*Csch[a+b*x^n]^p/(b*n*p) +
  Dist[(m-n+1)/(b*n*p),Int[x^(m-n)*Csch[a+b*x^n]^p,x]]) /;
FreeQ[{a,b,p},x] && RationalQ[m] && IntegerQ[n] && m-n>=0 && q===1

(* ::Code:: *)
Int[Sech[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
(Print["Int(72th)@HyperbolicSecantFunctions.m"];
  Int[(2/((c*x^n)^b+1/(c*x^n)^b))^p,x]) /;
FreeQ[c,x] && RationalQ[{b,n,p}]

(* ::Code:: *)
Int[Csch[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
(Print["Int(73th)@HyperbolicSecantFunctions.m"];
  Int[(2/((c*x^n)^b - 1/(c*x^n)^b))^p,x]) /;
FreeQ[c,x] && RationalQ[{b,n,p}]

(* ::Code:: *)
Int[Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(74th)@HyperbolicSecantFunctions.m"];
  x*Tanh[a+b*Log[c*x^n]]*Sech[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) + 
  x*Sech[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2))) /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[p-1] && ZeroQ[b^2*n^2*(p-2)^2-1]

(* ::Code:: *)
Int[Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(75th)@HyperbolicSecantFunctions.m"];
  -x*Coth[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  x*Csch[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2))) /;
FreeQ[{a,b,c,n,p},x] && NonzeroQ[p-1] && ZeroQ[b^2*n^2*(p-2)^2-1]

(* ::Code:: *)
Int[Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(76th)@HyperbolicSecantFunctions.m"];
  x*Tanh[a+b*Log[c*x^n]]*Sech[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) +
  x*Sech[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  Dist[(b^2*n^2*(p-2)^2-1)/(b^2*n^2*(p-1)*(p-2)),Int[Sech[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2-1]

(* ::Code:: *)
Int[Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(77th)@HyperbolicSecantFunctions.m"];
  -x*Coth[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  x*Csch[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) -
  Dist[(b^2*n^2*(p-2)^2-1)/(b^2*n^2*(p-1)*(p-2)),Int[Csch[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2-1]

(* ::Code:: *)
Int[Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(78th)@HyperbolicSecantFunctions.m"];
  -b*n*p*x*Sech[a+b*Log[c*x^n]]^(p+1)*Sinh[a+b*Log[c*x^n]]/(b^2*n^2*p^2-1) -
  x*Sech[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-1) +
  Dist[b^2*n^2*p*(p+1)/(b^2*n^2*p^2-1),Int[Sech[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2-1]

(* ::Code:: *)
Int[Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(79th)@HyperbolicSecantFunctions.m"];
  -b*n*p*x*Cosh[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2-1) - 
  x*Csch[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-1) -
  Dist[b^2*n^2*p*(p+1)/(b^2*n^2*p^2-1),Int[Csch[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2-1]

(* ::Code:: *)
Int[x_^m_.Sech[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
(Print["Int(80th)@HyperbolicSecantFunctions.m"];
  Int[x^m*(2/((c*x^n)^b+1/(c*x^n)^b))^p,x]) /;
FreeQ[c,x] && RationalQ[{b,m,n,p}]

(* ::Code:: *)
Int[x_^m_.*Csch[b_.*Log[c_.*x_^n_.]]^p_.,x_Symbol] :=
(Print["Int(81th)@HyperbolicSecantFunctions.m"];
  Int[x^m*(2/((c*x^n)^b - 1/(c*x^n)^b))^p,x]) /;
FreeQ[c,x] && RationalQ[{b,m,n,p}]

(* ::Code:: *)
Int[x_^m_.*Sec[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(82th)@HyperbolicSecantFunctions.m"];
  x^(m+1)*(b*n*(p-2)+(m+1)*Tan[a+b*Log[c*x^n]])*Sec[a+b*Log[c*x^n]]^(p-2)/(b*n*(m+1)*(p-1))) /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[m+1] && NonzeroQ[p-1] && ZeroQ[b^2*n^2*(p-2)^2+(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(83th)@HyperbolicSecantFunctions.m"];
  x^(m+1)*(b*n*(p-2)-(m+1)*Cot[a+b*Log[c*x^n]])*Csc[a+b*Log[c*x^n]]^(p-2)/(b*n*(m+1)*(p-1))) /;
FreeQ[{a,b,c,m,n,p},x] && NonzeroQ[m+1] && NonzeroQ[p-1] && ZeroQ[b^2*n^2*(p-2)^2+(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(84th)@HyperbolicSecantFunctions.m"];
  x^(m+1)*Tanh[a+b*Log[c*x^n]]*Sech[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) +
  (m+1)*x^(m+1)*Sech[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) +
  Dist[(b^2*n^2*(p-2)^2-(m+1)^2)/(b^2*n^2*(p-1)*(p-2)),Int[x^m*Sech[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2-(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(85th)@HyperbolicSecantFunctions.m"];
  -x^(m+1)*Coth[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p-2)/(b*n*(p-1)) -
  (m+1)*x^(m+1)*Csch[a+b*Log[c*x^n]]^(p-2)/(b^2*n^2*(p-1)*(p-2)) -
  Dist[(b^2*n^2*(p-2)^2-(m+1)^2)/(b^2*n^2*(p-1)*(p-2)),Int[x^m*Csch[a+b*Log[c*x^n]]^(p-2),x]]) /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p>1 && p!=2 && NonzeroQ[b^2*n^2*(p-2)^2-(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Sech[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(86th)@HyperbolicSecantFunctions.m"];
  -(m+1)*x^(m+1)*Sech[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-(m+1)^2) -
  b*n*p*x^(m+1)*Sech[a+b*Log[c*x^n]]^(p+1)*Sinh[a+b*Log[c*x^n]]/(b^2*n^2*p^2-(m+1)^2) +
  Dist[b^2*n^2*p*(p+1)/(b^2*n^2*p^2-(m+1)^2),Int[x^m*Sech[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2-(m+1)^2]

(* ::Code:: *)
Int[x_^m_.*Csch[a_.+b_.*Log[c_.*x_^n_.]]^p_,x_Symbol] :=
(Print["Int(87th)@HyperbolicSecantFunctions.m"];
  -(m+1)*x^(m+1)*Csch[a+b*Log[c*x^n]]^p/(b^2*n^2*p^2-(m+1)^2) -
  b*n*p*x^(m+1)*Cosh[a+b*Log[c*x^n]]*Csch[a+b*Log[c*x^n]]^(p+1)/(b^2*n^2*p^2-(m+1)^2) -
  Dist[b^2*n^2*p*(p+1)/(b^2*n^2*p^2-(m+1)^2),Int[x^m*Csch[a+b*Log[c*x^n]]^(p+2),x]]) /;
FreeQ[{a,b,c,m,n},x] && RationalQ[p] && p<-1 && NonzeroQ[b^2*n^2*p^2-(m+1)^2]

