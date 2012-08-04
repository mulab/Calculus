(* ::Package:: *)

Int[Sin[c_.+d_.*x_],x_Symbol] :=
(Print["Int(1th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Cos[c+d*x]/d) /;
FreeQ[{c,d},x]

Int[Cos[a_.+b_.*x_],x_Symbol] :=
(Print["Int(2th)@(sin^j)^m (a+b sin^k)^n.m"];
  Sin[a+b*x]/b) /;
FreeQ[{a,b},x]

Int[1/Sin[c_.+d_.*x_],x_Symbol] :=
(Print["Int(3th)@(sin^j)^m (a+b sin^k)^n.m"];
  -ArcTanh[Cos[c+d*x]]/d) /;
FreeQ[{c,d},x]

Int[Sec[a_.+b_.*x_],x_Symbol] :=
(Print["Int(4th)@(sin^j)^m (a+b sin^k)^n.m"];
  ArcTanh[Sin[a+b*x]]/b) /;
FreeQ[{a,b},x]

Int[Sin[c_.+d_.*x_]^2,x_Symbol] :=
(Print["Int(5th)@(sin^j)^m (a+b sin^k)^n.m"];
  x/2 - Cos[c+d*x]*Sin[c+d*x]/(2*d)) /;
FreeQ[{c,d},x]

Int[Cos[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(6th)@(sin^j)^m (a+b sin^k)^n.m"];
  x/2 + Cos[a+b*x]*Sin[a+b*x]/(2*b)) /;
FreeQ[{a,b},x]

Int[1/Sin[c_.+d_.*x_]^2,x_Symbol] :=
(Print["Int(7th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Cot[c+d*x]/d) /;
FreeQ[{c,d},x]

Int[Sec[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(8th)@(sin^j)^m (a+b sin^k)^n.m"];
  Tan[a+b*x]/b) /;
FreeQ[{a,b},x]

Int[Sin[c_.+d_.*x_]^m_,x_Symbol] :=
(Print["Int(9th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[-1/d,Subst[Int[Expand[(1+x^2)^((-m-2)/2),x],x],x,Cot[c+d*x]]]) /;
FreeQ[{c,d},x] && EvenQ[m] && m<-2

Int[Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(10th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[1/b,Subst[Int[Regularize[(1+x^2)^((n-2)/2),x],x],x,Tan[a+b*x]]]) /;
FreeQ[{a,b},x] && EvenQ[n] && n>2

Int[(Sin[c_.+d_.*x_]^j_.)^m_,x_Symbol] :=
(Print["Int(11th)@(sin^j)^m (a+b sin^k)^n.m"];
  2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+1)/(d*(2*m+j+1)) + 
  Dist[(2*m+j+3)/(2*m+j+1),Int[(Sin[c+d*x]^j)^(m+2),x]]) /;
FreeQ[{c,d},x] && OneQ[j^2] && Not[EvenQ[m]] && RationalQ[m] && m<-1

Int[Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(12th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Sin[a+b*x]*Cos[a+b*x]^(n+1)/(b*(n+1)) +
  Dist[(n+2)/(n+1),Int[Cos[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1

Int[Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(13th)@(sin^j)^m (a+b sin^k)^n.m"];
  Sin[a+b*x]*Sec[a+b*x]^(n-1)/(b*(n-1)) + 
  Dist[(n-2)/(n-1),Int[Sec[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n>1

Int[Sin[c_.+d_.*x_]^m_,x_Symbol] :=
(Print["Int(14th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[-1/d,Subst[Int[Expand[(1-x^2)^((m-1)/2),x],x],x,Cos[c+d*x]]]) /;
FreeQ[{c,d},x] && OddQ[m] && m>1

Int[Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(15th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[1/b,Subst[Int[Expand[(1-x^2)^((n-1)/2),x],x],x,Sin[a+b*x]]]) /;
FreeQ[{a,b},x] && OddQ[n] && n>1

Int[(Sin[c_.+d_.*x_]^j_.)^m_,x_Symbol] :=
(Print["Int(16th)@(sin^j)^m (a+b sin^k)^n.m"];
  -2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m-1)/(d*(2*m+j-1)) + 
  Dist[(2*m+j-3)/(2*m+j-1),Int[(Sin[c+d*x]^j)^(m-2),x]]) /;
FreeQ[{c,d},x] && OneQ[j^2] && Not[OddQ[m]] && RationalQ[m] && m>1

Int[Cos[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(17th)@(sin^j)^m (a+b sin^k)^n.m"];
  Sin[a+b*x]*Cos[a+b*x]^(n-1)/(b*n) +
  Dist[(n-1)/n,Int[Cos[a+b*x]^(n-2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n>1

Int[Sec[a_.+b_.*x_]^n_,x_Symbol] :=
(Print["Int(18th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Sin[a+b*x]*Sec[a+b*x]^(n+1)/(b*n) + 
  Dist[(n+1)/n,Int[Sec[a+b*x]^(n+2),x]]) /;
FreeQ[{a,b},x] && RationalQ[n] && n<-1

Int[1/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(19th)@(sin^j)^m (a+b sin^k)^n.m"];
  x/Rt[a^2-b^2,2] + 
  2/(d*Rt[a^2-b^2,2])*ArcTan[Simplify[b*Cos[c+d*x]/(a+Rt[a^2-b^2,2]+b*Sin[c + d*x])]]) /;
FreeQ[{a,b,c,d},x] && PositiveQ[a^2-b^2]

Int[1/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(20th)@(sin^j)^m (a+b sin^k)^n.m"];
  x/Rt[a^2-b^2,2] - 2/(d*Rt[a^2-b^2,2])*ArcTan[Simplify[b*Sin[c+d*x]/(a+Rt[a^2-b^2,2]+b*Cos[c + d*x])]]) /;
FreeQ[{a,b,c,d},x] && PositiveQ[a^2-b^2]

Int[1/(a_+b_.*Sin[c_.+Pi/2+d_.*x_]),x_Symbol] :=
(Print["Int(21th)@(sin^j)^m (a+b sin^k)^n.m"];
  2*ArcTan[(a-b)*Tan[(c+d*x)/2]/Rt[a^2-b^2,2]]/(d*Rt[a^2-b^2,2])) /;
FreeQ[{a,b,c,d},x] && PosQ[a^2-b^2]

Int[1/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(22th)@(sin^j)^m (a+b sin^k)^n.m"];
  2*ArcTan[(b+a*Tan[(c+d*x)/2])/Rt[a^2-b^2,2]]/(d*Rt[a^2-b^2,2])) /;
FreeQ[{a,b,c,d},x] && PosQ[a^2-b^2]

Int[1/(a_+b_.*Sin[c_.+Pi/2+d_.*x_]),x_Symbol] :=
(Print["Int(23th)@(sin^j)^m (a+b sin^k)^n.m"];
  -2*ArcTanh[(a-b)*Tan[(c+d*x)/2]/Rt[b^2-a^2,2]]/(d*Rt[b^2-a^2,2])) /;
FreeQ[{a,b,c,d},x] && NegQ[a^2-b^2]

Int[1/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(24th)@(sin^j)^m (a+b sin^k)^n.m"];
  -2*ArcTanh[(b+a*Tan[(c+d*x)/2])/Rt[b^2-a^2,2]]/(d*Rt[b^2-a^2,2])) /;
FreeQ[{a,b,c,d},x] && NegQ[a^2-b^2]

Int[1/(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(25th)@(sin^j)^m (a+b sin^k)^n.m"];
  x/a - Dist[b/a,Int[1/(b+a*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[(a_+b_.*Sin[c_.+d_.*x_]^k_.)^2,x_Symbol] :=
(Print["Int(26th)@(sin^j)^m (a+b sin^k)^n.m"];
  (a^2+(k+1)/(k+3)*b^2)*x - 2*b^2*Cos[c+d*x]*Sin[c+d*x]^k/(d*(k+3)) + 2*a*b*Int[Sin[c+d*x]^k,x]) /;
FreeQ[{a,b,c,d},x] && OneQ[k^2]

Int[Sqrt[a_.+b_.*Sin[c_.+Pi/2+d_.*x_]],x_Symbol] :=
(Print["Int(27th)@(sin^j)^m (a+b sin^k)^n.m"];
  2*Sqrt[Simplify[a+b]]/d*EllipticE[(c+d*x)/2,Simplify[2*b/(a+b)]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]

Int[Sqrt[a_.+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(28th)@(sin^j)^m (a+b sin^k)^n.m"];
  -2*Sqrt[Simplify[a+b]]/d*EllipticE[Pi/4-(c+d*x)/2,Simplify[2*b/(a+b)]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]

Int[Sqrt[a_.+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(29th)@(sin^j)^m (a+b sin^k)^n.m"];
  (a+b)*Sqrt[(a+b*Sin[c+d*x])/(a+b)]/Sqrt[a+b*Sin[c+d*x]]*Int[Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]

Int[1/Sqrt[a_.+b_.*Sin[c_.+Pi/2+d_.*x_]],x_Symbol] :=
(Print["Int(30th)@(sin^j)^m (a+b sin^k)^n.m"];
  2/(d*Sqrt[Simplify[a+b]])*EllipticF[(c+d*x)/2,Simplify[2*b/(a+b)]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]

Int[1/Sqrt[a_.+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(31th)@(sin^j)^m (a+b sin^k)^n.m"];
  -2/(d*Sqrt[Simplify[a+b]])*EllipticF[Pi/4-(c+d*x)/2,Simplify[2*b/(a+b)]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && PositiveQ[a+b]

Int[1/Sqrt[a_.+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(32th)@(sin^j)^m (a+b sin^k)^n.m"];
  Sqrt[(a+b*Sin[c+d*x])/(a+b)]/Sqrt[a+b*Sin[c+d*x]]*Int[1/Sqrt[a/(a+b)+b/(a+b)*Sin[c+d*x]],x]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && Not[PositiveQ[a+b]]

Int[(b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(33th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[Sin[c+d*x]^n*(b*Csc[c+d*x])^n,Int[1/Sin[c+d*x]^n,x]]) /;
FreeQ[{b,c,d},x] && ZeroQ[n^2-1/4]

Int[(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(34th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]]),
    Int[(b+a*Sin[c+d*x])^n/Sin[c+d*x]^n,x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && IntegerQ[n-1/2] && -2<n<2

Int[(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(35th)@(sin^j)^m (a+b sin^k)^n.m"];
  b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(a*(n+1)*(a^2-b^2)),
    Int[((a^2-b^2)*(n+1)-(a*b*(n+1))*Sin[c+d*x]^(-1)+(b^2*(n+2))*Sin[c+d*x]^(-2))*
      (a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(36th)@(sin^j)^m (a+b sin^k)^n.m"];
  -b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-2)/(d*(n-1)) + 
  Dist[1/(n-1),
    Int[(a^3*(n-1)+(b*(b^2*(n-2)+3*a^2*(n-1)))*Sin[c+d*x]^(-1)+(a*b^2*(3*n-4))*Sin[c+d*x]^(-2))*
      (a+b*Sin[c+d*x]^(-1))^(n-3),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>2

Int[(b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(37th)@(sin^j)^m (a+b sin^k)^n.m"];
  2*Cos[c+d*x]*(b*Sin[c+d*x]^k)^(n+1)/(b*d*(2*n+k+1)) + 
  Dist[(2*n+k+3)/(b^2*(2*n+k+1)),Int[(b*Sin[c+d*x]^k)^(n+2),x]]) /;
FreeQ[{b,c,d},x] && OneQ[k^2] && RationalQ[n] && n<-1

Int[(b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(38th)@(sin^j)^m (a+b sin^k)^n.m"];
  -2*b*Cos[c+d*x]*(b*Sin[c+d*x]^k)^(n-1)/(d*(2*n+k-1)) + 
  Dist[b^2*(2*n+k-3)/(2*n+k-1),Int[(b*Sin[c+d*x]^k)^(n-2),x]]) /;
FreeQ[{b,c,d},x] && OneQ[k^2] && RationalQ[n] && n>1

Int[1/(Sin[c_.+d_.*x_]*(a_.+b_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(39th)@(sin^j)^m (a+b sin^k)^n.m"];
  1/a*Int[1/Sin[c+d*x],x] - b/a*Int[1/(a+b*Sin[c+d*x]),x]) /;
FreeQ[{a,b,c,d},x]

Int[1/((a_.+b_.*Sin[c_.+d_.*x_])*(e_+f_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(40th)@(sin^j)^m (a+b sin^k)^n.m"];
  b/(b*e-a*f)*Int[1/(a+b*Sin[c+d*x]),x] - 
  f/(b*e-a*f)*Int[1/(e+f*Sin[c+d*x]),x]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[b*e-a*f]

Int[1/((a_.+b_.*Sin[c_.+Pi/2+d_.*x_])*Sqrt[e_.+f_.*Sin[c_.+Pi/2+d_.*x_]]),x_Symbol] :=
(Print["Int(41th)@(sin^j)^m (a+b sin^k)^n.m"];
  2/(d*(a+b)*Rt[e+f,2])*EllipticPi[Simplify[2*b/(a+b)],(c+d*x)/2,Simplify[2*f/(e+f)]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NonzeroQ[e^2-f^2] && PositiveQ[e+f]

Int[1/((a_.+b_.*Sin[c_.+d_.*x_])*Sqrt[e_.+f_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(42th)@(sin^j)^m (a+b sin^k)^n.m"];
  2/(d*(a+b)*Rt[e+f,2])*EllipticPi[Simplify[2*b/(a+b)],(c+d*x)/2-Pi/4,Simplify[2*f/(e+f)]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NonzeroQ[e^2-f^2] && PositiveQ[e+f]

Int[1/((a_.+b_.*Sin[c_.+d_.*x_])*Sqrt[e_.+f_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(43th)@(sin^j)^m (a+b sin^k)^n.m"];
  Sqrt[(e+f*Sin[c+d*x])/(e+f)]/Sqrt[e+f*Sin[c+d*x]]*
    Int[1/((a+b*Sin[c+d*x])*Sqrt[e/(e+f)+f/(e+f)*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && NonzeroQ[e^2-f^2] && Not[PositiveQ[e+f]]

Int[Sqrt[a_.+b_.*Sin[c_.+d_.*x_]]/(e_.+f_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(44th)@(sin^j)^m (a+b sin^k)^n.m"];
  b/f*Int[1/Sqrt[a+b*Sin[c+d*x]],x] + 
  (a*f-b*e)/f*Int[1/((e+f*Sin[c+d*x])*Sqrt[a+b*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NonzeroQ[e^2-f^2] && NonzeroQ[a*f-b*e]

Int[(a_.+b_.*Sin[c_.+d_.*x_])^(3/2)/(e_.+f_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(45th)@(sin^j)^m (a+b sin^k)^n.m"];
  b/f*Int[Sqrt[a+b*Sin[c+d*x]],x] + 
  Dist[(a*f-b*e)/f,Int[Sqrt[a+b*Sin[c+d*x]]/(e+f*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NonzeroQ[e^2-f^2] && NonzeroQ[a*f-b*e]

Int[1/(Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(46th)@(sin^j)^m (a+b sin^k)^n.m"];
  2/(d*Sqrt[a+b])*EllipticF[ArcSin[Tan[(c-Pi/2+d*x)/2]],-Simplify[(a-b)/(a+b)]]) /;
FreeQ[{a,b,c,d},x] && PositiveQ[b] && PositiveQ[b^2-a^2]

Int[1/(Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(47th)@(sin^j)^m (a+b sin^k)^n.m"];
  2*Sqrt[1+Sin[c+d*x]]/(d*Sqrt[a+b*Sin[c+d*x]])*
  Sqrt[(a+b*Sin[c+d*x])/((a+b)*(1+Sin[c+d*x]))]*
  EllipticF[ArcSin[Tan[(c-Pi/2+d*x)/2]],-Simplify[(a-b)/(a+b)]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(48th)@(sin^j)^m (a+b sin^k)^n.m"];
  -a*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[(a+a*Sin[c+d*x]+b*Sin[c+d*x]^2)/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[Sqrt[Sin[c_.+d_.*x_]]/Sqrt[a_+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(49th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] +
  Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[Sqrt[a_+b_.*Sin[c_.+d_.*x_]]/Sqrt[Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(50th)@(sin^j)^m (a+b sin^k)^n.m"];
  (a-b)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] +
  Dist[b,Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

(* Int[Sqrt[a_.+b_.*Sin[c_.+d_.*x_]]/Sqrt[e_.+f_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(51th)@(sin^j)^m (a+b sin^k)^n.m"];
  (a-b)*Int[1/(Sqrt[a+b*Sin[c+d*x]]*Sqrt[e+f*Sin[c+d*x]]),x] +
  Dist[b,Int[(1+Sin[c+d*x])/(Sqrt[a+b*Sin[c+d*x]]*Sqrt[e+f*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NonzeroQ[e^2-f^2] && NonzeroQ[b*e-a*f] *)

Int[Sqrt[Sin[c_.+d_.*x_]]/(a_+b_.*Sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
  -1/(a-b)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Dist[a/(a-b),Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x]] /; 
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[Sqrt[a_+b_.*Sin[c_.+d_.*x_]]/Sin[c_.+d_.*x_]^(3/2),x_Symbol] :=
  Dist[a+b,Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]] + 
  Dist[a,Int[(1-Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x]] /; 
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

(* Int[Sqrt[a_.+b_.*Sin[c_.+d_.*x_]]/(e_.+f_.*Sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
  Dist[(a-b)/(e-f),Int[1/(Sqrt[a+b*Sin[c+d*x]]*Sqrt[e+f*Sin[c+d*x]]),x]] + 
  Dist[(b*e-a*f)/(e-f),Int[(1+Sin[c+d*x])/(Sqrt[a+b*Sin[c+d*x]]*(e+f*Sin[c+d*x])^(3/2)),x]] /; 
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NonzeroQ[e^2-f^2] && NonzeroQ[b*e-a*f] *)

Int[Sin[c_.+d_.*x_]^(3/2)/Sqrt[a_+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(55th)@(sin^j)^m (a+b sin^k)^n.m"];
  -a/(2*b)*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Dist[1/(2*b),
    Int[(a+a*Sin[c+d*x]+2*b*Sin[c+d*x]^2)/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[(a_+b_.*Sin[c_.+d_.*x_])^(3/2)/Sqrt[Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(56th)@(sin^j)^m (a+b sin^k)^n.m"];
  3*a*b/2*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Dist[1/2,
    Int[(a*(2*a-3*b)+a*b*Sin[c+d*x]+2*b^2*Sin[c+d*x]^2)/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[Sin[c_.+d_.*x_]^(3/2)/(a_+b_.*Sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
(Print["Int(57th)@(sin^j)^m (a+b sin^k)^n.m"];
  1/b*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Dist[1/b,Int[(-a-(a+b)*Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[(a_+b_.*Sin[c_.+d_.*x_])^(3/2)/Sin[c_.+d_.*x_]^(3/2),x_Symbol] :=
(Print["Int(58th)@(sin^j)^m (a+b sin^k)^n.m"];
  b^2*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[(a^2+b*(2*a-b)*Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

(* Int[(a_.+b_.*Sin[c_.+d_.*x_])^(3/2)/(e_.+f_.*Sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
(Print["Int(59th)@(sin^j)^m (a+b sin^k)^n.m"];
  b^2/f*Int[(1+Sin[c+d*x])/(Sqrt[a+b*Sin[c+d*x]]*Sqrt[e+f*Sin[c+d*x]]),x] + 
  Dist[1/f,
    Int[(a^2*f-b^2*e+b*(2*a*f-b*(e+f))*Sin[c+d*x])/(Sqrt[a+b*Sin[c+d*x]]*(e+f*Sin[c+d*x])^(3/2)),x]]) /;
FreeQ[{a,b,c,d,e,f},x] && NonzeroQ[a^2-b^2] && NonzeroQ[e^2-f^2] && NonzeroQ[b*e-a*f] *)

Int[1/(Sqrt[Sin[c_.+d_.*x_]]*(a_+b_.*Sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
(Print["Int(60th)@(sin^j)^m (a+b sin^k)^n.m"];
  1/(a-b)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] - 
  Dist[b/(a-b),Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[1/(Sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(61th)@(sin^j)^m (a+b sin^k)^n.m"];
  Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[(1-Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

Int[Sqrt[a_+b_.*Sin[c_.+d_.*x_]]/(Sqrt[Sin[c_.+d_.*x_]]*(A_+B_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(62th)@(sin^j)^m (a+b sin^k)^n.m"];
  Sqrt[a+b]/(d*A)*EllipticE[ArcSin[Tan[(c-Pi/2+d*x)/2]],-Simplify[(a-b)/(a+b)]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && PositiveQ[b] && PositiveQ[b^2-a^2]

Int[Sqrt[a_+b_.*Sin[c_.+d_.*x_]]/(Sqrt[Sin[c_.+d_.*x_]]*(A_+B_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(63th)@(sin^j)^m (a+b sin^k)^n.m"];
  (a+b)*Sqrt[1+Sin[c+d*x]]/(d*A*Sqrt[a+b*Sin[c+d*x]])*Sqrt[(a+b*Sin[c+d*x])/((a+b)*(1+Sin[c+d*x]))]*
  EllipticE[ArcSin[Tan[(c-Pi/2+d*x)/2]],-Simplify[(a-b)/(a+b)]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && NonzeroQ[a^2-b^2]

Int[Sqrt[Sin[c_.+d_.*x_]]/(Sqrt[a_.+b_.*Sin[c_.+d_.*x_]]*(A_+B_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(64th)@(sin^j)^m (a+b sin^k)^n.m"];
  a/(A*(a-b))*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] - 
  1/(a-b)*Int[Sqrt[a+b*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*(A+B*Sin[c+d*x])),x]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && NonzeroQ[a^2-b^2]

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(65th)@(sin^j)^m (a+b sin^k)^n.m"];
  4*A/(d*Sqrt[a+b])*EllipticPi[-1,ArcSin[Tan[(c-Pi/2+d*x)/2]],-Simplify[(a-b)/(a+b)]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && PositiveQ[b] && PositiveQ[b^2-a^2]

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(66th)@(sin^j)^m (a+b sin^k)^n.m"];
  4*A*Sqrt[1+Sin[c+d*x]]/(d*Sqrt[a+b*Sin[c+d*x]])*
  Sqrt[(a+b*Sin[c+d*x])/((a+b)*(1+Sin[c+d*x]))]*
  EllipticPi[-1,ArcSin[Tan[(c-Pi/2+d*x)/2]],-Simplify[(a-b)/(a+b)]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A-B] && NonzeroQ[a^2-b^2]

Int[Sin[c_.+d_.*x_]^m_.*(b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(67th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[1/b^(k*m),Int[(b*Sin[c+d*x]^k)^(k*m+n),x]]) /;
FreeQ[{b,c,d,n},x] && OneQ[k^2] && IntegerQ[m]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(b_*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(68th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[b^(n-1/2)*Sqrt[b*Sin[c+d*x]^k]/(Sqrt[Sin[c+d*x]^j])^(j*k),Int[Sin[c+d*x]^(j*m+k*n),x]]) /;
FreeQ[{b,c,d},x] && OneQ[j^2,k^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && n>0

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(b_*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(69th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[b^(n+1/2)*(Sqrt[Sin[c+d*x]^j])^(j*k)/Sqrt[b*Sin[c+d*x]^k],Int[Sin[c+d*x]^(j*m+k*n),x]]) /;
FreeQ[{b,c,d},x] && OneQ[j^2,k^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_./(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(70th)@(sin^j)^m (a+b sin^k)^n.m"];
  Int[(Sin[c+d*x]^j)^(m+j)/(b+a*Sin[c+d*x]),x]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2] && NonzeroQ[a^2-b^2] && RationalQ[m] && -1/2<=m+j<=3/2

Int[Sin[c_.+d_.*x_]^m_.*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(71th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]]),
    Int[Sin[c+d*x]^(m-n)*(b+a*Sin[c+d*x])^n,x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && IntegerQ[m] && IntegerQ[n-1/2] && 
  (m==1 && -1<n<2 || m==-1 && -2<n<1  || m==-2 && -2<n<0)

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(72th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/((Sqrt[Sin[c+d*x]^j])^j*Sqrt[a+b*Csc[c+d*x]]),
    Int[Sin[c+d*x]^(j*m-n)*(b+a*Sin[c+d*x])^n,x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2] && NonzeroQ[a^2-b^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && 
  -1<n<2 && -1<=j*m-n<=1

Int[(Sin[c_.+d_.*x_]^(-1))^m_*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(73th)@(sin^j)^m (a+b sin^k)^n.m"];
  Dist[Sqrt[Csc[c+d*x]]*Sqrt[Sin[c+d*x]],
    Int[(a+b*Sin[c+d*x]^k)^n/Sin[c+d*x]^m,x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[k^2] && NonzeroQ[a^2-b^2] && IntegerQ[m-1/2] && RationalQ[n] && 
  (k===1 || -1<m<1 && -1<=n<1)

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^2,x_Symbol] :=
(Print["Int(74th)@(sin^j)^m (a+b sin^k)^n.m"];
  a^2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[2*a*b*(j*k*m+(k+1)/2)+(a^2+(a^2+b^2)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k,x],x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && RationalQ[m] && j*k*m+(k+1)/2!=0 && j*k*m<=-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^2,x_Symbol] :=
(Print["Int(75th)@(sin^j)^m (a+b sin^k)^n.m"];
  -b^2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+3)/2)) + 
  Dist[1/(j*k*m+(k+3)/2),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a^2+(a^2+b^2)*(j*k*m+(k+1)/2)+2*a*b*(j*k*m+(k+3)/2)*Sin[c+d*x]^k,x],x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && RationalQ[m] && j*k*m+(k+3)/2!=0 && j*k*m>=-1

Int[(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(76th)@(sin^j)^m (a+b sin^k)^n.m"];
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  Dist[1/((n+1)*(a^2-b^2)),Int[(a*(n+1)-b*(n+2)*Sin[c+d*x])*(a+b*Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[Sin[c_.+d_.*x_]^(-1)*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(77th)@(sin^j)^m (a+b sin^k)^n.m"];
  -b*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  Dist[1/((n+1)*(a^2-b^2)),Int[Sin[c+d*x]^(-1)*(a*(n+1)-b*(n+2)*Sin[c+d*x]^(-1))*(a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[(a_.+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(78th)@(sin^j)^m (a+b sin^k)^n.m"];
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n) + 
  Dist[1/n,Int[Simplify[a^2*n+b^2*(n-1)+a*b*(2*n-1)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n-2),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1

Int[Sin[c_.+d_.*x_]^(-1)*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(79th)@(sin^j)^m (a+b sin^k)^n.m"];
  -b*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-1)/(d*n) + 
  Dist[1/n,Int[Sin[c+d*x]^(-1)*(a^2*n+b^2*(n-1)+a*b*(2*n-1)*Sin[c+d*x]^(-1))*(a+b*Sin[c+d*x]^(-1))^(n-2),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1

Int[Sin[c_.+d_.*x_]^m_*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(80th)@(sin^j)^m (a+b sin^k)^n.m"];
  a*Cos[c+d*x]*Sin[c+d*x]^((k-1)/2)*(a+b*Sin[c+d*x]^k)^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  Dist[1/((n+1)*(a^2-b^2)),
    Int[Sin[c+d*x]^((k-1)/2)*(b*(n+1)-a*(n+2)*Sin[c+d*x]^k)*(a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[k^2] && ZeroQ[m-(3*k-1)/2] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[Sin[c_.+d_.*x_]^m_/(a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(81th)@(sin^j)^m (a+b sin^k)^n.m"];
  1/b*Int[Sin[c+d*x]^((k-1)/2),x] - 
  a/b*Int[Sin[c+d*x]^((k-1)/2)/(a+b*Sin[c+d*x]^k),x]) /;
FreeQ[{a,b,c,d},x] && OneQ[k^2] && ZeroQ[m-(3*k-1)/2] && NonzeroQ[a^2-b^2]

Int[Sin[c_.+d_.*x_]^m_*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(82th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Cos[c+d*x]*Sin[c+d*x]^((k-1)/2)*(a+b*Sin[c+d*x]^k)^n/(d*(n+1)) + 
  Dist[n/(n+1),
    Int[Sin[c+d*x]^((k-1)/2)*(b+a*Sin[c+d*x]^k)*(a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[k^2] && ZeroQ[m-(3*k-1)/2] && RationalQ[n] && n>-1

Int[Sin[c_.+d_.*x_]^m_*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(83th)@(sin^j)^m (a+b sin^k)^n.m"];
  -a^2*Cos[c+d*x]*Sin[c+d*x]^((k-1)/2)*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[Sin[c+d*x]^((k-1)/2)*(a*b*(n+1)-(a^2+b^2*(n+1))*Sin[c+d*x]^k)*(a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[k^2] && ZeroQ[m-(5*k-1)/2] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[Sin[c_.+d_.*x_]^m_/(a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(84th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Cos[c+d*x]*Sin[c+d*x]^((k-1)/2)/(b*d) - 
  Dist[a/b,Int[Sin[c+d*x]^((3*k-1)/2)/(a+b*Sin[c+d*x]^k),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[k^2] && ZeroQ[m-(5*k-1)/2]

Int[Sin[c_.+d_.*x_]^m_*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(85th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Cos[c+d*x]*Sin[c+d*x]^((k-1)/2)*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(n+2)) + 
  Dist[1/(b*(n+2)),
    Int[Sin[c+d*x]^((k-1)/2)*(b*(n+1)-a*Sin[c+d*x]^k)*(a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[k^2] && ZeroQ[m-(5*k-1)/2] && RationalQ[n] && n>-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(86th)@(sin^j)^m (a+b sin^k)^n.m"];
  -a^2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m-2*j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^(m-3*j*k)*
      Simplify[a^2*(j*k*m+(k-1)/2-2)+a*b*(n+1)*Sin[c+d*x]^k-
        (b^2*(n+1)+a^2*(j*k*m+(k-1)/2-1))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && j*k*m>2 && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(87th)@(sin^j)^m (a+b sin^k)^n.m"];
  a*Cos[c+d*x]*(Sin[c+d*x]^j)^(m-j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(d*(n+1)*(a^2-b^2)) - 
  Dist[1/((n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^(m-2*j*k)*
      Simplify[a*(j*k*m+(k-1)/2-1)+b*(n+1)*Sin[c+d*x]^k-a*(j*k*m+n+(k+1)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  1<j*k*m<2 && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(88th)@(sin^j)^m (a+b sin^k)^n.m"];
  -b*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  Dist[1/((n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[b*(j*k*m+(k-1)/2)+a*(n+1)*Sin[c+d*x]^k-b*(j*k*m+n+(k+1)/2+1)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  0<j*k*m<1 && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(a_.+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(89th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Cos[c+d*x]*(Sin[c+d*x]^j)^(m-2*j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(j*k*m+n+(k-1)/2)) + 
  Dist[1/(b*(j*k*m+n+(k-1)/2)),
    Int[(Sin[c+d*x]^j)^(m-3*j*k)*
      Simplify[a*(j*k*m+(k-1)/2-2)+b*(j*k*m+n+(k-1)/2-1)*Sin[c+d*x]^k-
        a*(j*k*m+(k-1)/2-1)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && j*k*m>2 && -1<=n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(a_.+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(90th)@(sin^j)^m (a+b sin^k)^n.m"];
  -Cos[c+d*x]*(Sin[c+d*x]^j)^(m-j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+n+(k-1)/2)) + 
  Dist[1/(j*k*m+n+(k-1)/2),
    Int[(Sin[c+d*x]^j)^(m-2*j*k)*
      Simplify[a*(j*k*m+(k-1)/2-1)+b*(j*k*m+n+(k-1)/2-1)*Sin[c+d*x]^k+a*n*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m>1 && j*k*m!=2 && 0<n<1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_.+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(91th)@(sin^j)^m (a+b sin^k)^n.m"];
  -b^2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-2)/(d*(j*k*m+n+(k-1)/2)) + 
  Dist[1/(j*k*m+n+(k-1)/2),
   Int[(Sin[c+d*x]^j)^m*
    Simplify[a*(a^2*(n-1)+(a^2+b^2)*(j*k*m+(k+1)/2))+b*(-b^2+(3*a^2+b^2)*(j*k*m+n+(k-1)/2))*Sin[c+d*x]^k+
      a*b^2*(2*j*k*m+3*n+k-3)*Sin[c+d*x]^(2*k),x]*
    (a+b*Sin[c+d*x]^k)^(n-3),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m>=-1 && j*k*m!=1 && j*k*m!=2 && n>2

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_.+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(92th)@(sin^j)^m (a+b sin^k)^n.m"];
  -b*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n-1)/(d*(j*k*m+n+(k-1)/2)) + 
  Dist[1/(j*k*m+n+(k-1)/2),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[a*b*(j*k*m+(k-1)/2)+((a^2+b^2)*(j*k*m+n+(k-1)/2)-b^2)*Sin[c+d*x]^k+
        a*b*(j*k*m+2*n+(k-1)/2-1)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-2),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m>0 && j*k*m!=1 && j*k*m!=2 && 1<n<2

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(93th)@(sin^j)^m (a+b sin^k)^n.m"];
  a^2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-2)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[a^2*b*(2*j*k*m-n+k+3)+a*(a^2+(a^2+3*b^2)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k+
        b*(a^2*(n-1)+(a^2+b^2)*(j*k*m+(k+1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-3),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m<-1 && n>2

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(94th)@(sin^j)^m (a+b sin^k)^n.m"];
  a*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-1)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[a*b*(j*k*m-n+(k+1)/2+1)+(a^2+(a^2+b^2)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k+
        a*b*(j*k*m+n+(k+1)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-2),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m<-1 && 1<n<2

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_.+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(95th)@(sin^j)^m (a+b sin^k)^n.m"];
  Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[-b*n+a*(j*k*m+(k+1)/2+1)*Sin[c+d*x]^k+b*(j*k*m+n+(k+1)/2+1)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m+(k+1)/2!=0 && j*k*m<=-1 && 0<n<1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(96th)@(sin^j)^m (a+b sin^k)^n.m"];
  Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(a*d*(j*k*m+(k+1)/2)) + 
  Dist[1/(a*(j*k*m+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[-b*(j*k*m+n+(k+1)/2+1)+a*(j*k*m+(k+1)/2+1)*Sin[c+d*x]^k+
        b*(j*k*m+n+(k+1)/2+2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m+(k+1)/2!=0 && j*k*m<=-1 && -1<=n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(97th)@(sin^j)^m (a+b sin^k)^n.m"];
  b^2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(a*(n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[(a^2-b^2)*(n+1)-b^2*(j*k*m+(k+1)/2)-a*b*(n+1)*Sin[c+d*x]^k+
        b^2*(j*k*m+n+(k+1)/2+2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m<0 && n<-1
