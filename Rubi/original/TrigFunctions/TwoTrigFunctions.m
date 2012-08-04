(* ::Package:: *)

(* ::Code:: *)
Int[x_*(A_+B_.*Sin[c_.+d_.*x_])/(a_+b_.*Sin[c_.+d_.*x_])^2,x_Symbol] :=
(Print["Int(1th)@TwoTrigFunctions.m"];
  -B*x*Cos[c+d*x]/(a*d*(a+b*Sin[c+d*x])) +
  Dist[B/(a*d),Int[Cos[c+d*x]/(a+b*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a*A-b*B]

(* ::Code:: *)
Int[x_*(A_+B_.*Cos[c_.+d_.*x_])/(a_+b_.*Cos[c_.+d_.*x_])^2,x_Symbol] :=
(Print["Int(2th)@TwoTrigFunctions.m"];
  B*x*Sin[c+d*x]/(a*d*(a+b*Cos[c+d*x])) -
  Dist[B/(a*d),Int[Sin[c+d*x]/(a+b*Cos[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a*A-b*B]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]*Tan[a_.+b_.*x_],x_Symbol] :=
(Print["Int(3th)@TwoTrigFunctions.m"];
  -Sin[a+b*x]/b + Int[Sec[a+b*x],x]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]*Cot[a_.+b_.*x_],x_Symbol] :=
(Print["Int(4th)@TwoTrigFunctions.m"];
  Cos[a+b*x]/b + Int[Csc[a+b*x],x]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(5th)@TwoTrigFunctions.m"];
  -Sin[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*m)) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n-1]

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(6th)@TwoTrigFunctions.m"];
  Cos[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*m)) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n-1]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_.*Tan[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(7th)@TwoTrigFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[(1-x^2)^((m+n-1)/2)/x^n,x],x],x,Cos[a+b*x]]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n,(m+n-1)/2]

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]^m_.*Cot[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(8th)@TwoTrigFunctions.m"];
  Dist[1/b,Subst[Int[Regularize[(1-x^2)^((m+n-1)/2)/x^n,x],x],x,Sin[a+b*x]]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n,(m+n-1)/2]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(9th)@TwoTrigFunctions.m"];
  Sin[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*m) -
  Dist[(n+1)/m,Int[Sin[a+b*x]^(m-2)*Tan[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(10th)@TwoTrigFunctions.m"];
  -Cos[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*m) -
  Dist[(n+1)/m,Int[Cos[a+b*x]^(m-2)*Cot[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(11th)@TwoTrigFunctions.m"];
  Sin[a+b*x]^(m+2)*Tan[a+b*x]^(n-1)/(b*(n-1)) -
  Dist[(m+2)/(n-1),Int[Sin[a+b*x]^(m+2)*Tan[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m<-1 && n>1

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(12th)@TwoTrigFunctions.m"];
  -Cos[a+b*x]^(m+2)*Cot[a+b*x]^(n-1)/(b*(n-1)) -
  Dist[(m+2)/(n-1),Int[Cos[a+b*x]^(m+2)*Cot[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m<-1 && n>1

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_.,x_Symbol]:=
  -Sin[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*m) +
  Dist[(m+n-1)/m,Int[Sin[a+b*x]^(m-2)*Tan[a+b*x]^n,x]] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(13th)@TwoTrigFunctions.m"];
  Cos[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*m) +
  Dist[(m+n-1)/m,Int[Cos[a+b*x]^(m-2)*Cot[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_.*Tan[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(14th)@TwoTrigFunctions.m"];
  Sin[a+b*x]^m*Tan[a+b*x]^(n-1)/(b*(n-1)) -
  Dist[(m+n-1)/(n-1),Int[Sin[a+b*x]^m*Tan[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]^m_.*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(15th)@TwoTrigFunctions.m"];
  -Cos[a+b*x]^m*Cot[a+b*x]^(n-1)/(b*(n-1)) -
  Dist[(m+n-1)/(n-1),Int[Cos[a+b*x]^m*Cot[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Tan[a_.+b_.*x_]^n_.,x_Symbol]:=
  Sin[a+b*x]^(m+2)*Tan[a+b*x]^(n-1)/(b*(m+n+1)) +
  Dist[(m+2)/(m+n+1),Int[Sin[a+b*x]^(m+2)*Tan[a+b*x]^n,x]] /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+1]

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]^m_*Cot[a_.+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(16th)@TwoTrigFunctions.m"];
  -Cos[a+b*x]^(m+2)*Cot[a+b*x]^(n-1)/(b*(m+n+1)) +
  Dist[(m+2)/(m+n+1),Int[Cos[a+b*x]^(m+2)*Cot[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+1]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_.*Tan[a_.+b_.*x_]^n_,x_Symbol]:=
  Sin[a+b*x]^m*Tan[a+b*x]^(n+1)/(b*(m+n+1)) -
  Dist[(n+1)/(m+n+1),Int[Sin[a+b*x]^m*Tan[a+b*x]^(n+2),x]] /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1]

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]^m_.*Cot[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(17th)@TwoTrigFunctions.m"];
  -Cos[a+b*x]^m*Cot[a+b*x]^(n+1)/(b*(m+n+1)) -
  Dist[(n+1)/(m+n+1),Int[Cos[a+b*x]^m*Cot[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+1]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]/Sqrt[Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(18th)@TwoTrigFunctions.m"];
  -ArcSin[Cos[a+b*x]-Sin[a+b*x]]/(2*b) - Log[Cos[a+b*x]+Sin[a+b*x]+Sqrt[Sin[c+d*x]]]/(2*b)) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-2*a] && ZeroQ[d-2*b]

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]/Sqrt[Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(19th)@TwoTrigFunctions.m"];
  -ArcSin[Cos[a+b*x]-Sin[a+b*x]]/(2*b) + Log[Cos[a+b*x]+Sin[a+b*x]+Sqrt[Sin[c+d*x]]]/(2*b)) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-2*a] && ZeroQ[d-2*b]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]/Sin[c_.+d_.*x_]^(3/2),x_Symbol] :=
(Print["Int(20th)@TwoTrigFunctions.m"];
  Sin[a+b*x]/(b*Sqrt[Sin[c+d*x]])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-2*a] && ZeroQ[d-2*b]

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]/Sin[c_.+d_.*x_]^(3/2),x_Symbol] :=
(Print["Int(21th)@TwoTrigFunctions.m"];
  -Cos[a+b*x]/(b*Sqrt[Sin[c+d*x]])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-2*a] && ZeroQ[d-2*b]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]*Sin[c_.+d_.*x_]^n_.,x_Symbol] :=
(Print["Int(22th)@TwoTrigFunctions.m"];
  -Cos[a+b*x]*Sin[c+d*x]^n/(b*(2*n+1)) + 
  Dist[2*n/(2*n+1),Int[Cos[a+b*x]*Sin[c+d*x]^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-2*a] && ZeroQ[d-2*b] && FractionQ[n] && n>0

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]*Sin[c_.+d_.*x_]^n_.,x_Symbol] :=
(Print["Int(23th)@TwoTrigFunctions.m"];
  Sin[a+b*x]*Sin[c+d*x]^n/(b*(2*n+1)) + 
  Dist[2*n/(2*n+1),Int[Sin[a+b*x]*Sin[c+d*x]^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-2*a] && ZeroQ[d-2*b] && FractionQ[n] && n>0

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]*Sin[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(24th)@TwoTrigFunctions.m"];
  -Sin[a+b*x]*Sin[c+d*x]^(n+1)/(2*b*(n+1)) + 
  Dist[(2*n+3)/(2*(n+1)),Int[Cos[a+b*x]*Sin[c+d*x]^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-2*a] && ZeroQ[d-2*b] && FractionQ[n] && n<-1 && n!=-3/2

(* ::Code:: *)
Int[Cos[a_.+b_.*x_]*Sin[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(25th)@TwoTrigFunctions.m"];
  Cos[a+b*x]*Sin[c+d*x]^(n+1)/(2*b*(n+1)) + 
  Dist[(2*n+3)/(2*(n+1)),Int[Sin[a+b*x]*Sin[c+d*x]^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-2*a] && ZeroQ[d-2*b] && FractionQ[n] && n<-1 && n!=-3/2

(* ::Code:: *)
Int[u_.*Sin[v_]*Cos[w_],x_Symbol] :=
(Print["Int(26th)@TwoTrigFunctions.m"];
  Dist[1/2,Int[u*Regularize[Sin[v+w],x],x]] + 
  Dist[1/2,Int[u*Regularize[Sin[v-w],x],x]]) /;
(PolynomialQ[v,x] && PolynomialQ[w,x] || IndependentQ[Cancel[v/w],x]) && NonzeroQ[v+w] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Sin[v_]*Sin[w_],x_Symbol] :=
(Print["Int(27th)@TwoTrigFunctions.m"];
  Dist[1/2,Int[u*Regularize[Cos[v-w],x],x]] - 
  Dist[1/2,Int[u*Regularize[Cos[v+w],x],x]]) /;
(PolynomialQ[v,x] && PolynomialQ[w,x] || IndependentQ[Cancel[v/w],x]) && NonzeroQ[v+w] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Cos[v_]*Cos[w_],x_Symbol] :=
(Print["Int(28th)@TwoTrigFunctions.m"];
  Dist[1/2,Int[u*Regularize[Cos[v-w],x],x]] + 
  Dist[1/2,Int[u*Regularize[Cos[v+w],x],x]]) /;
(PolynomialQ[v,x] && PolynomialQ[w,x] || IndependentQ[Cancel[v/w],x]) && NonzeroQ[v+w] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Sin[v_]*Tan[w_]^n_.,x_Symbol] :=
(Print["Int(29th)@TwoTrigFunctions.m"];
  -Int[u*Cos[v]*Tan[w]^(n-1),x] + Cos[v-w]*Int[u*Sec[w]*Tan[w]^(n-1),x]) /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Cos[v_]*Cot[w_]^n_.,x_Symbol] :=
(Print["Int(30th)@TwoTrigFunctions.m"];
  -Int[u*Sin[v]*Cot[w]^(n-1),x] + Cos[v-w]*Int[u*Csc[w]*Cot[w]^(n-1),x]) /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Sin[v_]*Cot[w_]^n_.,x_Symbol] :=
(Print["Int(31th)@TwoTrigFunctions.m"];
  Int[u*Cos[v]*Cot[w]^(n-1),x] + Sin[v-w]*Int[u*Csc[w]*Cot[w]^(n-1),x]) /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Cos[v_]*Tan[w_]^n_.,x_Symbol] :=
(Print["Int(32th)@TwoTrigFunctions.m"];
  Int[u*Sin[v]*Tan[w]^(n-1),x] - Sin[v-w]*Int[u*Sec[w]*Tan[w]^(n-1),x]) /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Sin[v_]*Sec[w_]^n_.,x_Symbol] :=
(Print["Int(33th)@TwoTrigFunctions.m"];
  Cos[v-w]*Int[u*Tan[w]*Sec[w]^(n-1),x] + Sin[v-w]*Int[u*Sec[w]^(n-1),x]) /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Cos[v_]*Csc[w_]^n_.,x_Symbol] :=
(Print["Int(34th)@TwoTrigFunctions.m"];
  Cos[v-w]*Int[u*Cot[w]*Csc[w]^(n-1),x] - Sin[v-w]*Int[u*Csc[w]^(n-1),x]) /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Sin[v_]*Csc[w_]^n_.,x_Symbol] :=
(Print["Int(35th)@TwoTrigFunctions.m"];
  Sin[v-w]*Int[u*Cot[w]*Csc[w]^(n-1),x] + Cos[v-w]*Int[u*Csc[w]^(n-1),x]) /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]

(* ::Code:: *)
Int[u_.*Cos[v_]*Sec[w_]^n_.,x_Symbol] :=
(Print["Int(36th)@TwoTrigFunctions.m"];
  -Sin[v-w]*Int[u*Tan[w]*Sec[w]^(n-1),x] + Cos[v-w]*Int[u*Sec[w]^(n-1),x]) /;
RationalQ[n] && n>0 && FreeQ[v-w,x] && NonzeroQ[v-w]

(* ::Code:: *)
Int[x_^m_.*Sin[a_.+b_.*x_^n_.]^p_.*Cos[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(37th)@TwoTrigFunctions.m"];
  x^(m-n+1)*Sin[a+b*x^n]^(p+1)/(b*n*(p+1)) -
  Dist[(m-n+1)/(b*n*(p+1)),Int[x^(m-n)*Sin[a+b*x^n]^(p+1),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n,p] && p!=-1 && 0<n<=m

(* ::Code:: *)
Int[x_^m_.*Cos[a_.+b_.*x_^n_.]^p_.*Sin[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(38th)@TwoTrigFunctions.m"];
  -x^(m-n+1)*Cos[a+b*x^n]^(p+1)/(b*n*(p+1)) +
  Dist[(m-n+1)/(b*n*(p+1)),Int[x^(m-n)*Cos[a+b*x^n]^(p+1),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n,p] && p!=-1 && 0<n<=m

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_.*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(39th)@TwoTrigFunctions.m"];
  Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n+1)/(b*(m+1))) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n+2] && NonzeroQ[m+1]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(40th)@TwoTrigFunctions.m"];
  Dist[1/b,Subst[Int[Regularize[x^m*(1-x^2)^((n-1)/2),x],x],x,Sin[a+b*x]]]) /;
FreeQ[{a,b,m},x] && OddQ[n] && Not[OddQ[m] && 0<m<n]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(41th)@TwoTrigFunctions.m"];
  Dist[-1/b,Subst[Int[Regularize[x^n*(1-x^2)^((m-1)/2),x],x],x,Cos[a+b*x]]]) /;
FreeQ[{a,b,n},x] && OddQ[m] && Not[OddQ[n] && 0<n<=m]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(42th)@TwoTrigFunctions.m"];
  -Sin[a+b*x]^(m-1)*Cos[a+b*x]^(n+1)/(b*(n+1)) +
  Dist[(m-1)/(n+1),Int[Sin[a+b*x]^(m-2)*Cos[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m>1 && n<-1

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(43th)@TwoTrigFunctions.m"];
  Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n-1)/(b*(m+1)) +
  Dist[(n-1)/(m+1),Int[Sin[a+b*x]^(m+2)*Cos[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m<-1 && n>1

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(44th)@TwoTrigFunctions.m"];
  -Sin[a+b*x]^(m-1)*Cos[a+b*x]^(n+1)/(b*(m+n)) +
  Dist[(m-1)/(m+n),Int[Sin[a+b*x]^(m-2)*Cos[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m>1 && NonzeroQ[m+n]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(45th)@TwoTrigFunctions.m"];
  Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n-1)/(b*(m+n)) +
  Dist[(n-1)/(m+n),Int[Sin[a+b*x]^m*Cos[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n>1 && NonzeroQ[m+n]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(46th)@TwoTrigFunctions.m"];
  Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n+1)/(b*(m+1)) +
  Dist[(m+n+2)/(m+1),Int[Sin[a+b*x]^(m+2)*Cos[a+b*x]^n,x]]) /;
FreeQ[{a,b,n},x] && RationalQ[m] && m<-1 && NonzeroQ[m+n+2]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(47th)@TwoTrigFunctions.m"];
  -Sin[a+b*x]^(m+1)*Cos[a+b*x]^(n+1)/(b*(n+1)) +
  Dist[(m+n+2)/(n+1),Int[Sin[a+b*x]^m*Cos[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b,m},x] && RationalQ[n] && n<-1 && NonzeroQ[m+n+2]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(48th)@TwoTrigFunctions.m"];
  Dist[1/(b*m),Subst[Int[x^(1/m)/(1+x^(2/m)),x],x,Sin[a+b*x]^m/Cos[a+b*x]^m]]) /;
FreeQ[{a,b},x] && ZeroQ[m+n] && IntegerQ[1/m] && 1/m>1

(* ::Code:: *)
Int[Sin[a_.+b_.*x_]^m_*Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(49th)@TwoTrigFunctions.m"];
  Dist[-1/(b*n),Subst[Int[x^(1/n)/(1+x^(2/n)),x],x,Cos[a+b*x]^n/Sin[a+b*x]^n]]) /;
FreeQ[{a,b},x] && ZeroQ[m+n] && IntegerQ[1/n] && 1/n>1

(* ::Code:: *)
Int[x_^m_./(a_.+b_.*Cos[d_.+e_.*x_]^2+c_.*Sin[d_.+e_.*x_]^2),x_Symbol] :=
(Print["Int(50th)@TwoTrigFunctions.m"];
  Dist[2,Int[x^m/(2*a+b+c+(b-c)*Cos[2*d+2*e*x]),x]]) /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && m>0 && NonzeroQ[a+b] && NonzeroQ[a+c]

(* ::Code:: *)
Int[x_^m_./(a_+b_.*Sin[c_.+d_.*x_]*Cos[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(51th)@TwoTrigFunctions.m"];
  Int[x^m/(a+b*Sin[2*c+2*d*x]/2),x]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[(a_+b_.*Sin[c_.+d_.*x_]*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(52th)@TwoTrigFunctions.m"];
  Int[(a+b*Sin[2*c+2*d*x]/2)^n,x]) /;
FreeQ[{a,b,c,d},x] && HalfIntegerQ[n]

(* ::Code:: *)
Int[Sin[a_.+b_.*x_^n_]^p_.*Cos[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
(Print["Int(53th)@TwoTrigFunctions.m"];
  Dist[1/2,Int[Sin[2*a+2*b*x^n]^p,x]]) /;
FreeQ[{a,b},x] && IntegersQ[n,p]

(* ::Code:: *)
Int[(a_.*Csc[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(54th)@TwoTrigFunctions.m"];
  Int[(a*Cos[c+d*x]*Cot[c+d*x])^n,x]) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a+b]

(* ::Code:: *)
Int[(a_.*Sec[c_.+d_.*x_]+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(55th)@TwoTrigFunctions.m"];
  Int[(a*Sin[c+d*x]*Tan[c+d*x])^n,x]) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a+b]

(* ::Code:: *)
Int[Sec[v_]^m_.*(a_+b_.*Tan[v_])^n_., x_Symbol] :=
(Print["Int(56th)@TwoTrigFunctions.m"];
  Int[(a*Cos[v]+b*Sin[v])^n,x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m+n==0 && OddQ[m]

(* ::Code:: *)
Int[Csc[v_]^m_.*(a_+b_.*Cot[v_])^n_., x_Symbol] :=
(Print["Int(57th)@TwoTrigFunctions.m"];
  Int[(b*Cos[v]+a*Sin[v])^n,x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m+n==0 && OddQ[m]

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*x_]^n_.*Sec[a_.+b_.*x_]^n_., x_Symbol] :=
(Print["Int(58th)@TwoTrigFunctions.m"];
  Dist[2^n,Int[x^m*Csc[2*a+2*b*x]^n,x]]) /;
FreeQ[{a,b},x] && RationalQ[m] && IntegerQ[n]

(* ::Code:: *)
Int[x_^m_.*Csc[a_.+b_.*x_]^n_.*Sec[a_.+b_.*x_]^p_., x_Symbol] :=
(Print["Int(59th)@TwoTrigFunctions.m"];
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[Csc[a+b*x]^n*Sec[a+b*x]^p,x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]]) /;
FreeQ[{a,b},x] && RationalQ[m] && IntegersQ[n,p] && m>0 && n!=p

(* ::Code:: *)
Int[(a_.*Tan[v_]+b_.*Sec[v_])^n_,x_Symbol] :=
(Print["Int(60th)@TwoTrigFunctions.m"];
  Dist[a^n,Int[Tan[v/2+Pi/4*a/b]^n,x]]) /;
FreeQ[{a,b},x] && ZeroQ[a^2-b^2] && EvenQ[n]

(* ::Code:: *)
Int[(a_.*Cot[v_]+b_.*Csc[v_])^n_,x_Symbol] :=
(Print["Int(61th)@TwoTrigFunctions.m"];
  Dist[a^n,Int[Cot[v/2+(a/b-1)*Pi/4]^n,x]]) /;
FreeQ[{a,b},x] && ZeroQ[a^2-b^2] && EvenQ[n]

(* ::Code:: *)
Int[u_.*(a_.*Sec[v_]^m_.+b_.*Tan[v_]^m_.)^n_.,x_Symbol] :=
(Print["Int(62th)@TwoTrigFunctions.m"];
  Int[u*(a+b*Sin[v]^m)^n/Cos[v]^(m*n),x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && (OddQ[m*n] || m*n<0) && Not[m==2 && ZeroQ[a+b]]

(* ::Code:: *)
Int[u_.*(a_.*Csc[v_]^m_.+b_.*Cot[v_]^m_.)^n_.,x_Symbol] :=
(Print["Int(63th)@TwoTrigFunctions.m"];
  Int[u*(a+b*Cos[v]^m)^n/Sin[v]^(m*n),x]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && (OddQ[m*n] || m*n<0) && Not[m==2 && ZeroQ[a+b]]

