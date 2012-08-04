(* ::Package:: *)

(* ::Code:: *)
Int[1/(a_+b_.*x_^n_),x_Symbol] :=
(Print["Int(1th)@AlgebraicFunctionsOfBinomials.m"];
  x/a - Dist[b/a,Int[1/(b+a*x^(-n)),x]]) /;
FreeQ[{a,b},x] && FractionQ[n] && n<0

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
(Print["Int(2th)@AlgebraicFunctionsOfBinomials.m"];
  ArcSinh[Rt[b,2]*x/Sqrt[a]]/Rt[b,2]) /;
FreeQ[{a,b},x] && PositiveQ[a] && PosQ[b]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
(Print["Int(3th)@AlgebraicFunctionsOfBinomials.m"];
  ArcSin[Rt[-b,2]*x/Sqrt[a]]/Rt[-b,2]) /;
FreeQ[{a,b},x] && PositiveQ[a] && NegQ[b]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
(Print["Int(4th)@AlgebraicFunctionsOfBinomials.m"];
  ArcTanh[Rt[b,2]*x/Sqrt[a+b*x^2]]/Rt[b,2]) /;
FreeQ[{a,b},x] && Not[PositiveQ[a]] && PosQ[b]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_^2],x_Symbol] :=
(Print["Int(5th)@AlgebraicFunctionsOfBinomials.m"];
  ArcTan[Rt[-b,2]*x/Sqrt[a+b*x^2]]/Rt[-b,2]) /;
FreeQ[{a,b},x] && Not[PositiveQ[a]] && NegQ[b]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
(Print["Int(6th)@AlgebraicFunctionsOfBinomials.m"];
  EllipticF[ArcSin[Rt[-b/a,4]*x],-1]/(Sqrt[a]*Rt[-b/a,4])) /;
FreeQ[{a,b},x] && PositiveQ[a]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_^4],x_Symbol] :=
(Print["Int(7th)@AlgebraicFunctionsOfBinomials.m"];
  Sqrt[(a+b*x^4)/a]/(Rt[-b/a,4]*Sqrt[a+b*x^4])*EllipticF[ArcSin[Rt[-b/a,4]*x],-1]) /;
FreeQ[{a,b},x] && Not[PositiveQ[a]]

(* ::Code:: *)
Int[x_^2/Sqrt[a_+b_.*x_^4],x_Symbol] :=
(Print["Int(8th)@AlgebraicFunctionsOfBinomials.m"];
  1/(Sqrt[a]*Rt[-b/a,4]^3)*EllipticE[ArcSin[Rt[-b/a,4]*x],-1] -
  1/(Sqrt[a]*Rt[-b/a,4]^3)*EllipticF[ArcSin[Rt[-b/a,4]*x],-1]) /;
FreeQ[{a,b},x] && PositiveQ[a]

(* ::Code:: *)
Int[x_^2/Sqrt[a_+b_.*x_^4],x_Symbol] :=
(Print["Int(9th)@AlgebraicFunctionsOfBinomials.m"];
  Sqrt[(a+b*x^4)/a]/(Rt[-b/a,4]^3*Sqrt[a+b*x^4])*EllipticE[ArcSin[Rt[-b/a,4]*x],-1] -
  Sqrt[(a+b*x^4)/a]/(Rt[-b/a,4]^3*Sqrt[a+b*x^4])*EllipticF[ArcSin[Rt[-b/a,4]*x],-1]) /;
FreeQ[{a,b},x] && Not[PositiveQ[a]]

(* ::Code:: *)
Int[Sqrt[a_.+b_./x_^2],x_Symbol] :=
(Print["Int(10th)@AlgebraicFunctionsOfBinomials.m"];
  -Subst[Int[Sqrt[a+b*x^2]/x^2,x],x,1/x]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(11th)@AlgebraicFunctionsOfBinomials.m"];
  x*(a+b*x^n)^(p+1)/a) /;
FreeQ[{a,b,n,p},x] && ZeroQ[n*(p+1)+1]

(* ::Code:: *)
Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(12th)@AlgebraicFunctionsOfBinomials.m"];
  x*(a+b*x^n)^p/(n*p+1) +
  Dist[a*n*p/(n*p+1),Int[(a+b*x^n)^(p-1),x]]) /;
FreeQ[{a,b,n},x] && FractionQ[p] && p>0 && NonzeroQ[n*p+1]

(* ::Code:: *)
Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(13th)@AlgebraicFunctionsOfBinomials.m"];
  -x*(a+b*x^n)^(p+1)/(n*(p+1)*a) +
  Dist[(n*(p+1)+1)/(a*n*(p+1)),Int[(a+b*x^n)^(p+1),x]]) /;
FreeQ[{a,b,n},x] && FractionQ[p] && p<-1

(* ::Code:: *)
Int[(a_+b_./x_)^p_,x_Symbol] :=
(Print["Int(14th)@AlgebraicFunctionsOfBinomials.m"];
  x*(a+b/x)^(p+1)/a +
  Dist[b*p/a,Int[(a+b/x)^p/x,x]]) /;
FreeQ[{a,b,p},x] && Not[IntegerQ[p]]

(* ::Code:: *)
Int[(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(15th)@AlgebraicFunctionsOfBinomials.m"];
  Module[{q=Denominator[p]},
  Dist[q*a^(p+1/n)/n,
	Subst[Int[x^(q/n-1)/(1-b*x^q)^(p+1/n+1),x],x,x^(n/q)/(a+b*x^n)^(1/q)]]]) /;
FreeQ[{a,b},x] && RationalQ[{p,n}] && -1<p<0 && IntegerQ[p+1/n]

(* ::Code:: *)
Int[(a_+b_.*(c_.*x_^n_)^m_)^p_.,x_Symbol] :=
(Print["Int(16th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[x/(c*x^n)^(1/n),Subst[Int[(a+b*x^(m*n))^p,x],x,(c*x^n)^(1/n)]]) /;
FreeQ[{a,b,c,m,n,p},x] && IntegerQ[m*n]

(* ::Code:: *)
Int[x_^m_.*(a_.+b_.*x_^n_)^p_.,x_Symbol] :=
(Print["Int(17th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[1/(m+1),Subst[Int[(a+b*x^(n/(m+1)))^p,x],x,x^(m+1)]]) /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+1] && IntegerQ[n/(m+1)] && n/(m+1)>1 && Not[IntegersQ[m,n,p]]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(18th)@AlgebraicFunctionsOfBinomials.m"];
  Int[x^(m+n*p)*(b+a/x^n)^p,x]) /;
FreeQ[{a,b,m},x] && IntegerQ[p] && p<0 && FractionQ[n] && n<0

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(19th)@AlgebraicFunctionsOfBinomials.m"];
  x^(m+1)*(a+b*x^n)^p/(m+1) -
  Dist[b*n*p/(m+1),Int[x^(m+n)*(a+b*x^n)^(p-1),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && FractionQ[p] && p>0 && (n>0 && m<-1 || 0<-n<=m+1)

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(20th)@AlgebraicFunctionsOfBinomials.m"];
  x^(m-n+1)*(a+b*x^n)^(p+1)/(b*n*(p+1)) -
  Dist[(m-n+1)/(b*n*(p+1)),Int[x^(m-n)*(a+b*x^n)^(p+1),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && FractionQ[p] && p<-1 && (0<n<=m || m<=n<0) && NonzeroQ[m-n+1]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(21th)@AlgebraicFunctionsOfBinomials.m"];
  x^(m+1)*(a+b*x^n)^p/(m+n*p+1) +
  Dist[n*p*a/(m+n*p+1),Int[x^m*(a+b*x^n)^(p-1),x]]) /;
FreeQ[{a,b,m,n,p},x] && FractionQ[p] && p>0 && NonzeroQ[m+n*p+1] &&
Not[IntegerQ[(m+1)/n] && (m+1)/n>0]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(22th)@AlgebraicFunctionsOfBinomials.m"];
  -x^(m+1)*(a+b*x^n)^(p+1)/(a*n*(p+1)) +
  Dist[(m+n*(p+1)+1)/(a*n*(p+1)),Int[x^m*(a+b*x^n)^(p+1),x]]) /;
FreeQ[{a,b,m,n},x] && FractionQ[p] && p<-1 && NonzeroQ[m+n*(p+1)+1] && NonzeroQ[m-n+1]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
(Print["Int(23th)@AlgebraicFunctionsOfBinomials.m"];
  x^(m-n+1)*(a+b*x^n)^(p+1)/(b*(m+n*p+1)) -
  Dist[a*(m-n+1)/(b*(m+n*p+1)),Int[x^(m-n)*(a+b*x^n)^p,x]]) /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+n*p+1] && NonzeroQ[m-n+1] && NonzeroQ[m+1] &&
Not[IntegersQ[m,n,p]] && 
	(IntegersQ[m,n] && (0<n<=m || m<=n<0) && (Not[RationalQ[p]] || -1<p<0) || 
 	IntegerQ[(m+1)/n] && 0<(m+1)/n && Not[FractionQ[n]] || 
     Not[RationalQ[m]] && RationalQ[m-n] || 
     RationalQ[n] && MatchQ[m,u_+q_ /; RationalQ[q] && (0<n<=q || n<0 && q<0)] || 
     MatchQ[m,u_+q_.*n /; RationalQ[q] && q>=1])

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_.)^p_,x_Symbol] :=
(Print["Int(24th)@AlgebraicFunctionsOfBinomials.m"];
  x^(m+1)*(a+b*x^n)^(p+1)/(a*(m+1)) -
  Dist[b*(m+n*(p+1)+1)/(a*(m+1)),Int[x^(m+n)*(a+b*x^n)^p,x]]) /;
FreeQ[{a,b,m,n,p},x] && NonzeroQ[m+1] && NonzeroQ[m+n*(p+1)+1] && Not[IntegersQ[m,n,p]] && 
	(IntegersQ[m,n] && (n>0 && m<-1 || 0<-n<=m+1) ||
     Not[RationalQ[m]] && RationalQ[m+n] ||
     RationalQ[n] && MatchQ[m,u_+q_ /; RationalQ[q] && (n>0 && q<0 || 0<-n<=q)] || 
     MatchQ[m,u_+q_*n /; RationalQ[q] && q<0])

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_)^p_,x_Symbol] :=
(Print["Int(25th)@AlgebraicFunctionsOfBinomials.m"];
  Module[{q=Denominator[p]},
  q*a^(p+(m+1)/n)/n*
	Subst[Int[x^(q*(m+1)/n-1)/(1-b*x^q)^(p+(m+1)/n+1),x],x,x^(n/q)/(a+b*x^n)^(1/q)]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n,p}] && -1<p<0 && IntegerQ[p+(m+1)/n] && GCD[m+1,n]==1

(* ::Code:: *)
Int[(x_^m_.*(a_+b_.*x_^n_.))^p_,x_Symbol] :=
(Print["Int(26th)@AlgebraicFunctionsOfBinomials.m"];
  (x^m*(a+b*x^n))^(p+1)/(b*n*(p+1)*x^(m*(p+1)))) /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m*p-n+1] && NonzeroQ[p+1]

(* ::Code:: *)
Int[(x_^m_.*(a_+b_.*x_^n_.))^p_.,x_Symbol] :=
(Print["Int(27th)@AlgebraicFunctionsOfBinomials.m"];
  -(x^m*(a+b*x^n))^(p+1)/(a*n*(p+1)*x^(m-1))) /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[m*p+n*(p+1)+1] && NonzeroQ[p+1]

(* ::Code:: *)
Int[x_^q_.*(x_^m_.*(a_+b_.*x_^n_.))^p_,x_Symbol] :=
(Print["Int(28th)@AlgebraicFunctionsOfBinomials.m"];
  (x^m*(a+b*x^n))^(p+1)/(b*n*(p+1)*x^(m*(p+1)))) /;
FreeQ[{a,b,m,n,p},x] && ZeroQ[q+m*p-n+1] && NonzeroQ[p+1]

(* ::Code:: *)
Int[x_^q_.*(x_^m_.*(a_+b_.*x_^n_.))^p_.,x_Symbol] :=
(Print["Int(29th)@AlgebraicFunctionsOfBinomials.m"];
  -(x^m*(a+b*x^n))^(p+1)/(a*n*(p+1)*x^(m-1-q))) /;
FreeQ[{a,b,m,n,p,q},x] && ZeroQ[q+m*p+n*(p+1)+1] && NonzeroQ[p+1]

(* ::Code:: *)
Int[(a_+b_.*x_^2)^m_.*(c_+d_.*x_^2)^n_,x_Symbol] :=
(Print["Int(30th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[(b/d)^m,Int[(c+d*x^2)^(n+m),x]]) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[b*c-a*d] && IntegerQ[m]

(* ::Code:: *)
Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
(Print["Int(31th)@AlgebraicFunctionsOfBinomials.m"];
  ArcTanh[x*Rt[(a*d-b*c)/a,2]/Sqrt[c+d*x^2]]/(a*Rt[(a*d-b*c)/a,2])) /;
FreeQ[{a,b,c,d},x] && PosQ[(a*d-b*c)/a]

(* ::Code:: *)
Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
(Print["Int(32th)@AlgebraicFunctionsOfBinomials.m"];
  ArcTan[x*Rt[(b*c-a*d)/a,2]/Sqrt[c+d*x^2]]/(a*Rt[(b*c-a*d)/a,2])) /;
FreeQ[{a,b,c,d},x] && NegQ[(a*d-b*c)/a]

(* ::Code:: *)
Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
(Print["Int(33th)@AlgebraicFunctionsOfBinomials.m"];
  1/(Sqrt[a]*Sqrt[c]*Rt[-d/c,2])*EllipticF[ArcSin[Rt[-d/c,2]*x], b*c/(a*d)]) /;
FreeQ[{a,b,c,d},x] && PositiveQ[a] && PositiveQ[c] &&
(PosQ[-c*d] && (NegQ[-a*b] || Not[RationalQ[Rt[-a*b,2]]]) || NegQ[-c*d] && NegQ[-a*b] &&
Not[RationalQ[Rt[a*b,2]]])

(* ::Code:: *)
Int[1/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
(Print["Int(34th)@AlgebraicFunctionsOfBinomials.m"];
  Sqrt[(a+b*x^2)/a]*Sqrt[(c+d*x^2)/c]/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2])*Int[1/(Sqrt[1+b/a*x^2]*Sqrt[1+d/c*x^2]),x]) /;
FreeQ[{a,b,c,d},x] && Not[PositiveQ[a] && PositiveQ[c]] &&
(PosQ[-c*d] && (NegQ[-a*b] || Not[RationalQ[Rt[-a*b,2]]]) || NegQ[-c*d] && NegQ[-a*b] &&
Not[RationalQ[Rt[a*b,2]]])

(* ::Code:: *)
Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
(Print["Int(35th)@AlgebraicFunctionsOfBinomials.m"];
  Sqrt[a]/(Sqrt[c]*Rt[-d/c,2])*EllipticE[ArcSin[Rt[-d/c,2]*x], b*c/(a*d)]) /;
FreeQ[{a,b,c,d},x] && PositiveQ[a] && PositiveQ[c]

(* ::Code:: *)
Int[Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
(Print["Int(36th)@AlgebraicFunctionsOfBinomials.m"];
  Sqrt[a+b*x^2]*Sqrt[(c+d*x^2)/c]/(Sqrt[c+d*x^2]*Sqrt[(a+b*x^2)/a])*Int[Sqrt[1+b/a*x^2]/Sqrt[1+d/c*x^2],x]) /;
FreeQ[{a,b,c,d},x] && Not[PositiveQ[a] && PositiveQ[c]]

(* ::Code:: *)
Int[Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2],x_Symbol] :=
(Print["Int(37th)@AlgebraicFunctionsOfBinomials.m"];
  x/3*Sqrt[a+b*x^2]*Sqrt[c+d*x^2] + 
  Dist[(c*b+a*d)/(3*d),Int[Sqrt[c+d*x^2]/Sqrt[a+b*x^2],x]] - 
  Dist[c*(c*b-a*d)/(3*d),Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[c*b+a*d] && NonzeroQ[c*b-a*d]

(* ::Code:: *)
Int[(a_+b_.*x_^2)^m_.*(c_+d_.*x_^2)^n_*(e_+f_.*x_^2)^p_,x_Symbol] :=
(Print["Int(38th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[(b/d)^m,Int[(c+d*x^2)^(m+n)*(e+f*x^2)^p,x]]) /;
FreeQ[{a,b,c,d,e,f,n,p},x] && ZeroQ[b*c-a*d] && IntegerQ[m]

(* ::Code:: *)
Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
(Print["Int(39th)@AlgebraicFunctionsOfBinomials.m"];
  1/(a*Sqrt[c]*Sqrt[e]*Rt[-d/c,2])*EllipticPi[b*c/(a*d), ArcSin[Rt[-d/c,2]*x], c*f/(e*d)]) /;
FreeQ[{a,b,c,d,e,f},x] && PositiveQ[c] && PositiveQ[e] &&
(PosQ[-e*f] && (NegQ[-c*d] || Not[RationalQ[Rt[-c*d,2]]]) || NegQ[-e*f] && NegQ[-c*d] &&
Not[RationalQ[Rt[c*d,2]]])

(* ::Code:: *)
Int[1/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]),x_Symbol] :=
(Print["Int(40th)@AlgebraicFunctionsOfBinomials.m"];
  Sqrt[(c+d*x^2)/c]*Sqrt[(e+f*x^2)/e]/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2])*
    Int[1/((a+b*x^2)*Sqrt[1+d/c*x^2]*Sqrt[1+f/e*x^2]),x]) /;
FreeQ[{a,b,c,d,e,f},x] && Not[PositiveQ[c] && PositiveQ[e]] &&
(PosQ[-e*f] && (NegQ[-c*d] || Not[RationalQ[Rt[-c*d,2]]]) || NegQ[-e*f] && NegQ[-c*d] &&
Not[RationalQ[Rt[c*d,2]]])

(* ::Code:: *)
Int[Sqrt[e_+f_.*x_^2]/((a_+b_.*x_^2)*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
(Print["Int(41th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[f/b,Int[1/(Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x]] + 
  Dist[(b*e-a*f)/b,Int[1/((a+b*x^2)*Sqrt[c+d*x^2]*Sqrt[e+f*x^2]),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*e-a*f]

(* ::Code:: *)
Int[Sqrt[c_+d_.*x_^2]*Sqrt[e_+f_.*x_^2]/(a_+b_.*x_^2),x_Symbol] :=
(Print["Int(42th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[d/b,Int[Sqrt[e+f*x^2]/Sqrt[c+d*x^2],x]] + 
  Dist[(b*c-a*d)/b,Int[Sqrt[e+f*x^2]/((a+b*x^2)*Sqrt[c+d*x^2]),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*c-a*d]

(* ::Code:: *)
Int[(e_.+f_.*x_^2)/(Sqrt[a_+b_.*x_^2]*Sqrt[c_+d_.*x_^2]),x_Symbol] :=
(Print["Int(43th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[f/b,Int[Sqrt[a+b*x^2]/Sqrt[c+d*x^2],x]] +
  Dist[(b*e-a*f)/b,Int[1/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*e-a*f] &&
(PosQ[-c*d] && (NegQ[-a*b] || Not[RationalQ[Rt[-a*b,2]]]) || NegQ[-c*d] && NegQ[-a*b] &&
Not[RationalQ[Rt[a*b,2]]])

(* ::Code:: *)
Int[x_^2*Sqrt[a_+b_.*x_^2]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
(Print["Int(44th)@AlgebraicFunctionsOfBinomials.m"];
  x*Sqrt[a+b*x^2]*Sqrt[c+d*x^2]/(3*d) -
  Dist[1/(3*d),Int[(a*c+(2*b*c-a*d)*x^2)/(Sqrt[a+b*x^2]*Sqrt[c+d*x^2]),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[(a_.+b_.*x_^n_)^p_*(c_.+d_.*x_^n_)^q_.,x_Symbol] :=
(Print["Int(45th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[b/d,Int[(a+b*x^n)^(p-1)*(c+d*x^n)^(q+1),x]]) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a*d-b*c] && RationalQ[{p,q}] && p>0 && q<=-1

(* ::Code:: *)
Int[(a_.+b_.*x_^n_)^p_*(c_.+d_.*x_^n_)^q_.,x_Symbol] :=
(Print["Int(46th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[(a*d-b*c)/d,Int[(a+b*x^n)^(p-1)*(c+d*x^n)^q,x]] +
  Dist[b/d,Int[(a+b*x^n)^(p-1)*(c+d*x^n)^(q+1),x]]) /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[a*d-b*c] && RationalQ[{p,q}] && p>0 && q<=-1 && 
IntegerQ[n] && n>0

(* ::Code:: *)
Int[(a_.+b_.*x_^n_)^p_.*(c_.+d_.*x_^n_)^q_.,x_Symbol] :=
(Print["Int(47th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[b/(b*c-a*d),Int[(a+b*x^n)^p*(c+d*x^n)^(q+1),x]] -
  Dist[d/(b*c-a*d),Int[(a+b*x^n)^(p+1)*(c+d*x^n)^q,x]]) /;
FreeQ[{a,b,c,d,n},x] && NonzeroQ[b*c-a*d] && RationalQ[{p,q}] && p<-1 && q<=-1 && 
IntegerQ[n] && n>0

(* ::Code:: *)
Int[(a_.+b_.*x_^n_.)/(x_*(c_+d_.*x_^p_.)),x_Symbol] :=
(Print["Int(48th)@AlgebraicFunctionsOfBinomials.m"];
  a*Log[x]/c +
  Dist[1/c,Int[x^(n-1)*(b*c-a*d*x^(p-n))/(c+d*x^p),x]]) /;
FreeQ[{a,b,c,d},x] && FractionQ[{n,p}] && 0<n<=p

(* ::Code:: *)
Int[(a_.+b_.*x_^n_.)/(x_*(c_+d_.*x_^p_.)),x_Symbol] :=
(Print["Int(49th)@AlgebraicFunctionsOfBinomials.m"];
  a*Log[x]/c +
  Dist[1/c,Int[x^(p-1)*(-a*d+b*c*x^(n-p))/(c+d*x^p),x]]) /;
FreeQ[{a,b,c,d},x] && FractionQ[{n,p}] && 0<p<n

(* ::Code:: *)
Int[x_^m_*(a_.+b_.*x_^n_.)/(c_+d_.*x_^p_.),x_Symbol] :=
(Print["Int(50th)@AlgebraicFunctionsOfBinomials.m"];
  a*x^(m+1)/(c*(m+1)) +
  Dist[1/c,Int[x^(m+n)*(b*c-a*d*x^(p-n))/(c+d*x^p),x]]) /;
FreeQ[{a,b,c,d},x] && FractionQ[{m,n,p}] && m<-1 && 0<n<=p

(* ::Code:: *)
Int[x_^m_*(a_.+b_.*x_^n_.)/(c_+d_.*x_^p_.),x_Symbol] :=
(Print["Int(51th)@AlgebraicFunctionsOfBinomials.m"];
  a*x^(m+1)/(c*(m+1)) +
  Dist[1/c,Int[x^(m+p)*(-a*d+b*c*x^(n-p))/(c+d*x^p),x]]) /;
FreeQ[{a,b,c,d},x] && FractionQ[{m,n,p}] && m<-1 && 0<p<n

(* ::Code:: *)
Int[1/Sqrt[c_.*x_^2*(a_.+b_./x_)],x_Symbol] :=
(Print["Int(52th)@AlgebraicFunctionsOfBinomials.m"];
  Int[1/Sqrt[b*c*x+a*c*x^2],x]) /;
FreeQ[{a,b,c},x] && NegativeQ[b^2*c/a]

(* ::Code:: *)
Int[1/Sqrt[c_.*x_^2*(a_.+b_.*x_^n_.)],x_Symbol] :=
(Print["Int(53th)@AlgebraicFunctionsOfBinomials.m"];
  -2/(n*Rt[a*c,2])*ArcTanh[Rt[a*c,2]*x/Sqrt[c*x^2*(a+b*x^n)]]) /;
FreeQ[{a,b,c,n},x] && PosQ[a*c]

(* ::Code:: *)
Int[1/Sqrt[c_.*x_^2*(a_.+b_.*x_^n_.)],x_Symbol] :=
(Print["Int(54th)@AlgebraicFunctionsOfBinomials.m"];
  -2/(n*Rt[-a*c,2])*ArcTan[Rt[-a*c,2]*x/Sqrt[c*x^2*(a+b*x^n)]]) /;
FreeQ[{a,b,c,n},x] && NegQ[a*c]

(* ::Code:: *)
Int[1/Sqrt[c_.*x_^m_.*(a_.+b_.*x_^n_.)],x_Symbol] :=
(Print["Int(55th)@AlgebraicFunctionsOfBinomials.m"];
  Int[1/Sqrt[c*x^2*(b+a*x^(m-2))],x]) /;
FreeQ[{a,b,c,m,n},x] && ZeroQ[m+n-2]

(* ::Code:: *)
Int[1/Sqrt[c_.*(a_.*x_^p_+b_.*x_^2)],x_Symbol] :=
(Print["Int(56th)@AlgebraicFunctionsOfBinomials.m"];
  Int[1/Sqrt[c*x^2*(b+a*x^(p-2))],x]) /;
FreeQ[{a,b,c,p},x]

(* ::Code:: *)
Int[1/Sqrt[c_.*x_^m_.*(a_.*x_^p_.+b_.*x_^n_.)],x_Symbol] :=
(Print["Int(57th)@AlgebraicFunctionsOfBinomials.m"];
  Int[1/Sqrt[c*x^2*(b+a*x^(m+p-2))],x]) /;
FreeQ[{a,b,c,m,n,p},x] && ZeroQ[m+n-2]

(* ::Code:: *)
(* Int[(e_.*(a_.+b_.*x_)/(c_.+d_.*x_))^n_,x_Symbol] :=
(Print["Int(58th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[e*(b*c-a*d),Subst[Int[x^n/(b*e-d*x)^2,x],x,e*(a+b*x)/(c+d*x)]]) /;
FreeQ[{a,b,c,d,e},x] && FractionQ[n] && NonzeroQ[b*c-a*d] *)

(* ::Code:: *)
(* Int[x_^m_.*(e_.*(a_.+b_.*x_)/(c_.+d_.*x_))^n_,x_Symbol] :=
(Print["Int(59th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[e*(b*c-a*d),Subst[Int[x^n*(-a*e+c*x)^m/(b*e-d*x)^(m+2),x],x,e*(a+b*x)/(c+d*x)]]) /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[m] && FractionQ[n] && NonzeroQ[b*c-a*d] *)

(* ::Code:: *)
(* Int[(f_+g_.*x_)^m_*(e_.*(a_.+b_.*x_)/(c_.+d_.*x_))^n_,x_Symbol] :=
(Print["Int(60th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[1/g,Subst[Int[x^m*(e*(a-b*f/g+b/g*x)/(c-d*f/g+d/g*x))^n,x],x,f+g*x]]) /;
FreeQ[{a,b,c,d,e,f,g},x] && IntegerQ[m] && m<0 && FractionQ[n] && NonzeroQ[b*c-a*d] *)

(* ::Code:: *)
Int[Sqrt[a_.*x_+Sqrt[b_+c_.*x_^2]], x_Symbol] :=
(Print["Int(61th)@AlgebraicFunctionsOfBinomials.m"];
  2*(2*a*x-Sqrt[b+c*x^2])*Sqrt[a*x+Sqrt[b+c*x^2]]/(3*a)) /;
FreeQ[{a,b,c},x] && ZeroQ[c-a^2]

(* ::Code:: *)
Int[Sqrt[a_.*x_-Sqrt[b_+c_.*x_^2]], x_Symbol] :=
(Print["Int(62th)@AlgebraicFunctionsOfBinomials.m"];
  2*(2*a*x+Sqrt[b+c*x^2])*Sqrt[a*x-Sqrt[b+c*x^2]]/(3*a)) /;
FreeQ[{a,b,c},x] && ZeroQ[c-a^2]

(* ::Code:: *)
Int[Sqrt[a_+Sqrt[c_+b_.*x_^2]], x_Symbol] :=
(Print["Int(63th)@AlgebraicFunctionsOfBinomials.m"];
  2*(-a^2+b*x^2+a*Sqrt[a^2+b*x^2])*Sqrt[a+Sqrt[a^2+b*x^2]]/(3*b*x)) /;
FreeQ[{a,b,c},x] && ZeroQ[c-a^2]

(* ::Code:: *)
Int[Sqrt[a_-Sqrt[c_+b_.*x_^2]], x_Symbol] :=
(Print["Int(64th)@AlgebraicFunctionsOfBinomials.m"];
  2*(-a^2+b*x^2-a*Sqrt[a^2+b*x^2])*Sqrt[a-Sqrt[a^2+b*x^2]]/(3*b*x)) /;
FreeQ[{a,b,c},x] && ZeroQ[c-a^2]

(* ::Code:: *)
Int[u_./(a_.*x_^m_.+b_.*Sqrt[c_.*x_^n_]),x_Symbol] :=
(Print["Int(65th)@AlgebraicFunctionsOfBinomials.m"];
  Int[u*(a*x^m-b*Sqrt[c*x^n])/(a^2*x^(2*m)-b^2*c*x^n),x]) /;
FreeQ[{a,b,c,m,n},x]

(* ::Code:: *)
Int[u_.*(e_.*Sqrt[a_.+b_.*x_^n_.]+f_.*Sqrt[c_.+d_.*x_^n_.])^m_,x_Symbol] :=
(Print["Int(66th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[(a*e^2-c*f^2)^m,Int[u*(e*Sqrt[a+b*x^n]-f*Sqrt[c+d*x^n])^(-m),x]]) /;
FreeQ[{a,b,c,d,e,f,n},x] && IntegerQ[m] && m<0 && ZeroQ[b*e^2-d*f^2]

(* ::Code:: *)
Int[u_.*(e_.*Sqrt[a_.+b_.*x_^n_.]+f_.*Sqrt[c_.+d_.*x_^n_.])^m_,x_Symbol] :=
(Print["Int(67th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[(b*e^2-d*f^2)^m,Int[u*x^(m*n)*(e*Sqrt[a+b*x^n]-f*Sqrt[c+d*x^n])^(-m),x]]) /;
FreeQ[{a,b,c,d,e,f,n},x] && IntegerQ[m] && m<0 && ZeroQ[a*e^2-c*f^2]

(* ::Code:: *)
Int[u_./(a_+b_.*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
(Print["Int(68th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[-a/(b^2*d),Int[u/x^n,x]] +
  Dist[1/(b*d),Int[u*Sqrt[c+d*x^n]/x^n,x]]) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2*c]

(* ::Code:: *)
Int[u_./(a_.*x_^m_.+b_.*Sqrt[c_+d_.*x_^n_]),x_Symbol] :=
(Print["Int(69th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[-a/(b^2*c),Int[u*x^m,x]] +
  Dist[1/(b*c),Int[u*Sqrt[c+d*x^n],x]]) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[n-2*m] && ZeroQ[a^2-b^2*d]

(* ::Code:: *)
Int[u_./(a_+b_.*x_^m_.+c_.*Sqrt[d_+e_.*x_^n_]),x_Symbol] :=
(Print["Int(70th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[1/(2*a),Int[u,x]] +
  Dist[1/(2*b),Int[u/x^m,x]] -
  Dist[c/(2*a*b),Int[u*Sqrt[d+e*x^n]/x^m,x]]) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[n-2*m] && ZeroQ[a^2-c^2*d] && ZeroQ[b^2-c^2*e]

(* ::Code:: *)
Int[u_./(a_+b_.*x_^n_.+c_.*Sqrt[d_+e_.*x_^n_.]),x_Symbol] :=
(Print["Int(71th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[1/b,Int[u/x^n,x]] +
  Dist[a/b^2,Int[u/x^(2*n),x]] -
  Dist[c/b^2,Int[u*Sqrt[d+e*x^n]/x^(2*n),x]]) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-c^2*d] && ZeroQ[2*a*b-c^2*e]

(* ::Code:: *)
(* Int[u_./(e_.*Sqrt[a_.+b_.*x_]+f_.*Sqrt[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(72th)@AlgebraicFunctionsOfBinomials.m"];
  Int[u*(e*Sqrt[a+b*x]-f*Sqrt[c+d*x])/(a*e^2-c*f^2+(b*e^2-d*f^2)*x),x]) /;
FreeQ[{a,b,c,d,e,f},x] *)

(* ::Code:: *)
Int[u_./(a_.*x_+b_.*Sqrt[c_.+d_.*x_^2]),x_Symbol] :=
(Print["Int(73th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[a,Int[x*u/(-b^2*c+(a^2-b^2*d)*x^2),x]] -
  Dist[b,Int[u*Sqrt[c+d*x^2]/(-b^2*c+(a^2-b^2*d)*x^2),x]]) /;
FreeQ[{a,b,c,d},x]

(* ::Code:: *)
Int[u_./(e_.*Sqrt[(a_.+b_.*x_^n_.)^p_.]+f_.*Sqrt[(a_.+b_.*x_^n_.)^q_.]),x_Symbol] :=
(Print["Int(74th)@AlgebraicFunctionsOfBinomials.m"];
  Int[u*(e*Sqrt[(a+b*x^n)^p]-f*Sqrt[(a+b*x^n)^q])/(e^2*(a+b*x^n)^p-f^2*(a+b*x^n)^q),x]) /;
FreeQ[{a,b,e,f},x] && IntegersQ[n,p,q]

(* ::Code:: *)
(* Int[u_./(v_+a_.*Sqrt[w_]),x_Symbol] :=
(Print["Int(75th)@AlgebraicFunctionsOfBinomials.m"];
  Int[u*v/(v^2-a^2*w),x] -
  Dist[a,Int[u*Sqrt[w]/(v^2-a^2*w),x]]) /;
FreeQ[a,x] && PolynomialQ[v,x] *)

(* ::Code:: *)
(* Int[u_./(a_.*x_+b_.*Sqrt[c_+d_.*x_]),x_Symbol] :=
(Print["Int(76th)@AlgebraicFunctionsOfBinomials.m"];
  Int[(a*x*u-b*u*Sqrt[c+d*x])/(-b^2*c-b^2*d*x+a^2*x^2),x]) /;
FreeQ[{a,b,c,d},x] *)

(* ::Code:: *)
Int[u_.*Sqrt[c_+d_.*x_^2]/(a_+b_.*x_),x_Symbol] :=
(Print["Int(77th)@AlgebraicFunctionsOfBinomials.m"];
  a*Int[u/Sqrt[c+d*x^2],x] -
  b*Int[x*u/Sqrt[c+d*x^2],x]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[c-a^2] && ZeroQ[d+b^2]

(* ::Code:: *)
Int[Sqrt[b_.*x_^2+Sqrt[a_+c_.*x_^4]]/Sqrt[a_+c_.*x_^4],x_Symbol] :=
(Print["Int(78th)@AlgebraicFunctionsOfBinomials.m"];
  ArcTanh[Rt[2*b,2]*x/Sqrt[b*x^2+Sqrt[a+c*x^4]]]/Rt[2*b,2]) /;
FreeQ[{a,b,c},x] && ZeroQ[c-b^2] && PosQ[b]

(* ::Code:: *)
Int[Sqrt[b_.*x_^2+Sqrt[a_+c_.*x_^4]]/Sqrt[a_+c_.*x_^4],x_Symbol] :=
(Print["Int(79th)@AlgebraicFunctionsOfBinomials.m"];
  ArcTan[Rt[-2*b,2]*x/Sqrt[b*x^2+Sqrt[a+c*x^4]]]/Rt[-2*b,2]) /;
FreeQ[{a,b,c},x] && ZeroQ[c-b^2] && NegQ[b]

(* ::Code:: *)
Int[u_.*Sqrt[v_+Sqrt[a_+w_]]/Sqrt[a_+w_],x_Symbol] :=
(Print["Int(80th)@AlgebraicFunctionsOfBinomials.m"];
  Dist[(1-I)/2, Int[u/Sqrt[Sqrt[a]-I*v],x]] +
  Dist[(1+I)/2, Int[u/Sqrt[Sqrt[a]+I*v],x]]) /;
FreeQ[a,x] && ZeroQ[w-v^2] && PositiveQ[a] && Not[LinearQ[v,x]]

(* ::Code:: *)
If[ShowSteps,

Int[1/(a_+b_.*u_),x_Symbol] :=
(Print["Int(81th)@AlgebraicFunctionsOfBinomials.m"];
  Module[{lst=ConstantFactor[a+b*u,x]},
  ShowStep["","Int[1/(a*c+b*c*u),x]","Int[1/(a+b*u),x]/c",Hold[
  Dist[1/lst[[1]],Int[1/lst[[2]],x]]]] /;
 lst[[1]]=!=1]) /;
SimplifyFlag && FreeQ[{a,b},x] && (
	MatchQ[u,f_^(c_.+d_.*x) /; FreeQ[{c,d,f},x]] ||
	MatchQ[u,f_[c_.+d_.*x] /; FreeQ[{c,d},x] && MemberQ[{Tan,Cot,Tanh,Coth},f]]),

Int[1/(a_+b_.*u_),x_Symbol] :=
(Print["Int(82th)@AlgebraicFunctionsOfBinomials.m"];
  Module[{lst=ConstantFactor[a+b*u,x]},
  Dist[1/lst[[1]],Int[1/lst[[2]],x]] /;
 lst[[1]]=!=1]) /;
FreeQ[{a,b},x] && (
	MatchQ[u,f_^(c_.+d_.*x) /; FreeQ[{c,d,f},x]] ||
	MatchQ[u,f_[c_.+d_.*x] /; FreeQ[{c,d},x] && MemberQ[{Tan,Cot,Tanh,Coth},f]])]
