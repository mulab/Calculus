(* ::Package:: *)

(* ::Code:: *)
Int[(a_.*Cosh[c_.+d_.*x_]+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(1th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  a*(a*Cosh[c+d*x]+b*Sinh[c+d*x])^n/(b*d*n)) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2-b^2]

(* ::Code:: *)
Int[1/(a_.*Cosh[c_.+d_.*x_]+b_.*Sinh[c_.+d_.*x_])^2,x_Symbol] :=
(Print["Int(2th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  Sinh[c+d*x]/(a*d*(a*Cosh[c+d*x]+b*Sinh[c+d*x]))) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2]

(* ::Code:: *)
Int[(a_.*Cosh[c_.+d_.*x_]+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(3th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  Dist[1/d,Subst[Int[Regularize[(a^2-b^2+x^2)^((n-1)/2),x],x],x,b*Cosh[c+d*x]+a*Sinh[c+d*x]]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && OddQ[n] && n>0

(* ::Code:: *)
Int[(a_.*Cosh[c_.+d_.*x_]+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(4th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (b*Cosh[c+d*x]+a*Sinh[c+d*x])*(a*Cosh[c+d*x]+b*Sinh[c+d*x])^(n-1)/(d*n) +
  Dist[(n-1)*(a^2-b^2)/n,Int[(a*Cosh[c+d*x]+b*Sinh[c+d*x])^(n-2),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1 && Not[OddQ[n]]

(* ::Code:: *)
Int[(a_.*Cosh[c_.+d_.*x_]+b_.*Sinh[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(5th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -(b*Cosh[c+d*x]+a*Sinh[c+d*x])*(a*Cosh[c+d*x]+b*Sinh[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) +
  Dist[(n+2)/((n+1)*(a^2-b^2)),Int[(a*Cosh[c+d*x]+b*Sinh[c+d*x])^(n+2),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[Cosh[c_.+d_.*x_]^m_.*Sinh[c_.+d_.*x_]^n_.*(a_.*Cosh[c_.+d_.*x_]+b_.*Sinh[c_.+d_.*x_])^p_,x_Symbol] :=
(Print["Int(6th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -Dist[b/(a^2-b^2),Int[Cosh[c+d*x]^m*Sinh[c+d*x]^(n-1)*(a*Cosh[c+d*x]+b*Sinh[c+d*x])^(p+1),x]] +
  Dist[a/(a^2-b^2),Int[Cosh[c+d*x]^(m-1)*Sinh[c+d*x]^n*(a*Cosh[c+d*x]+b*Sinh[c+d*x])^(p+1),x]] +
  Dist[a*b/(a^2-b^2),Int[Cosh[c+d*x]^(m-1)*Sinh[c+d*x]^(n-1)*(a*Cosh[c+d*x]+b*Sinh[c+d*x])^p,x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && IntegersQ[m,n,p] && m>0 && n>0 && p<0

(* ::Code:: *)
Int[u_.*Sinh[c_.+d_.*x_]^n_/(a_.*Cosh[c_.+d_.*x_]+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(7th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  Dist[-b/(a^2-b^2),Int[u*Sinh[c+d*x]^(n-1),x]] +
  Dist[a/(a^2-b^2),Int[u*Sinh[c+d*x]^(n-2)*Cosh[c+d*x],x]] -
  Dist[a^2/(a^2-b^2),Int[u*Sinh[c+d*x]^(n-2)/(a*Cosh[c+d*x]+b*Sinh[c+d*x]),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && IntegerQ[n] && n>0 && 
(n>1 || MatchQ[u,v_.*Tanh[c+d*x]^m_. /; IntegerQ[m] && m>0])

(* ::Code:: *)
Int[u_.*Cosh[c_.+d_.*x_]^n_/(a_.*Cosh[c_.+d_.*x_]+b_.*Sinh[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(8th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  Dist[a/(a^2-b^2),Int[u*Cosh[c+d*x]^(n-1),x]] -
  Dist[b/(a^2-b^2),Int[u*Cosh[c+d*x]^(n-2)*Sinh[c+d*x],x]] -
  Dist[b^2/(a^2-b^2),Int[u*Cosh[c+d*x]^(n-2)/(a*Cosh[c+d*x]+b*Sinh[c+d*x]),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2-b^2] && IntegerQ[n] && n>0 && 
(n>1 || MatchQ[u,v_.*Coth[c+d*x]^m_. /; IntegerQ[m] && m>0])

(* ::Code:: *)
Int[1/(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(9th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  Log[a+c*Tanh[(d+e*x)/2]]/(c*e)) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a-b]

(* ::Code:: *)
Int[1/(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(10th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -Log[a-c*Coth[(d+e*x)/2]]/(c*e)) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a+b]

(* ::Code:: *)
Int[1/(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(11th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -(c+a*Sinh[d+e*x])/(c*e*(c*Cosh[d+e*x]+b*Sinh[d+e*x]))) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2+c^2]

(* ::Code:: *)
Int[1/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(12th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -2*ArcTanh[(c-(a-b)*Tanh[(d+e*x)/2])/Rt[a^2-b^2+c^2,2]]/(e*Rt[a^2-b^2+c^2,2])) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2] && PosQ[a^2-b^2+c^2]

(* ::Code:: *)
Int[1/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(13th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  2*ArcTan[(c-(a-b)*Tanh[(d+e*x)/2])/Rt[-a^2+b^2-c^2,2]]/(e*Rt[-a^2+b^2-c^2,2])) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2] && NegQ[a^2-b^2+c^2]

(* ::Code:: *)
Int[Sqrt[a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]],x_Symbol] :=
(Print["Int(14th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  2*(c*Cosh[d+e*x]+b*Sinh[d+e*x])/(e*Sqrt[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]])) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2+c^2]

(* ::Code:: *)
Int[Sqrt[a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]],x_Symbol] :=
(Print["Int(15th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  Int[Sqrt[a-I*Sqrt[b^2-c^2]*Sinh[d+e*x+I*ArcTan[I*c,b]]],x]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2+c^2] && PositiveQ[a-Sqrt[b^2-c^2]]

(* ::Code:: *)
Int[Sqrt[a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]],x_Symbol] :=
(Print["Int(16th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  2*I*EllipticE[(Pi/2-I*(d+e*x+I*ArcTan[I*c,b]))/2,2/(1-a/Sqrt[b^2-c^2])]*
  Sqrt[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/
  (e*Sqrt[(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])/(a-Sqrt[b^2-c^2])])) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2+c^2] && Not[PositiveQ[a-Sqrt[b^2-c^2]]]

(* ::Code:: *)
Int[1/Sqrt[a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]],x_Symbol] :=
(Print["Int(17th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  Int[1/Sqrt[a-I*Sqrt[b^2-c^2]*Sinh[d+e*x+I*ArcTan[I*c,b]]],x]) /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[a-Sqrt[b^2-c^2]]

(* ::Code:: *)
Int[1/Sqrt[a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]],x_Symbol] :=
(Print["Int(18th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  2*I*EllipticF[(Pi/2-I*(d+e*x+I*ArcTan[I*c,b]))/2,2/(1-a/Sqrt[b^2-c^2])]*
  Sqrt[(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])/(a-Sqrt[b^2-c^2])]/
  (e*Sqrt[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]])) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a-Sqrt[b^2-c^2]] && Not[PositiveQ[a-Sqrt[b^2-c^2]]]

(* ::Code:: *)
Int[(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(19th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (c*Cosh[d+e*x]+b*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n-1)/(e*n) +
  Dist[a*(2*n-1)/n,Int[(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n-1),x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2+c^2] && RationalQ[n] && n>1

(* ::Code:: *)
Int[(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(20th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (c*Cosh[d+e*x]+b*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n-1)/(e*n) +
  Dist[1/n,Int[(n*a^2+(n-1)*(b^2-c^2)+a*b*(2*n-1)*Cosh[d+e*x]+a*c*(2*n-1)*Sinh[d+e*x])*
    (a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n-2),x]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2+c^2] && RationalQ[n] && n>1

(* ::Code:: *)
Int[(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(21th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -(c*Cosh[d+e*x]+b*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^n/(a*e*(2*n+1)) +
  Dist[(n+1)/(a*(2*n+1)),Int[(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2+c^2] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[1/(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^2,x_Symbol] :=
(Print["Int(22th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -(c*Cosh[d+e*x]+b*Sinh[d+e*x])/(e*(a^2-b^2+c^2)*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])) +
  Dist[a/(a^2-b^2+c^2),Int[1/(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]),x]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2+c^2]

(* ::Code:: *)
Int[1/(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^(3/2),x_Symbol] :=
(Print["Int(23th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -2*(c*Cosh[d+e*x]+b*Sinh[d+e*x])/(e*(a^2-b^2+c^2)*Sqrt[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]) +
  Dist[1/(a^2-b^2+c^2),Int[Sqrt[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]],x]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2+c^2]

(* ::Code:: *)
Int[(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(24th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (c*Cosh[d+e*x]+b*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1)/(e*(n+1)*(a^2-b^2+c^2)) +
  1/((n+1)*(a^2-b^2+c^2))*
    Int[((n+1)*a-(n+2)*b*Cosh[d+e*x]-(n+2)*c*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1),x]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2+c^2] && RationalQ[n] && n<-1 && n!=-2 && n!=-3/2

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_]+C_.*Sinh[d_.+e_.*x_])/(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(25th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (2*a*A-b*B+c*C)*x/(2*a^2) - (b*B-c*C)*(b*Cosh[d+e*x]-c*Sinh[d+e*x])/(2*a*b*c*e) + 
  (a^2*(b*B+c*C)-2*a*A*b^2+b^2*(b*B-c*C))*Log[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/(2*a^2*b*c*e)) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && ZeroQ[b^2-c^2]

(* ::Code:: *)
Int[(A_.+C_.*Sinh[d_.+e_.*x_])/(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(26th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (2*a*A+c*C)*x/(2*a^2) + C*Cosh[d+e*x]/(2*a*e) - c*C*Sinh[d+e*x]/(2*a*b*e) + 
  (a^2*C-2*a*c*A-b^2*C)*Log[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/(2*a^2*b*e)) /;
FreeQ[{a,b,c,d,e,A,C},x] && ZeroQ[b^2-c^2]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_])/(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(27th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (2*a*A-b*B)*x/(2*a^2) - b*B*Cosh[d+e*x]/(2*a*c*e) + B*Sinh[d+e*x]/(2*a*e) + 
  (a^2*B-2*a*b*A+b^2*B)*Log[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/(2*a^2*c*e)) /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2-c^2]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_]+C_.*Sinh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(28th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (b*B-c*C)*x/(b^2-c^2) - (c*B-b*C)*Log[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/(e*(b^2-c^2))) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[b^2-c^2] && ZeroQ[A*(b^2-c^2)-a*(b*B-c*C)]

(* ::Code:: *)
Int[(A_.+C_.*Sinh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(29th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -c*C*x/(b^2-c^2) + b*C*Log[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/(e*(b^2-c^2))) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[b^2-c^2] && ZeroQ[A*(b^2-c^2)+a*c*C]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(30th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  b*B*x/(b^2-c^2) - c*B*Log[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/(e*(b^2-c^2))) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-c^2] && ZeroQ[A*(b^2-c^2)-a*b*B]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_]+C_.*Sinh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(31th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (b*B-c*C)*x/(b^2-c^2) - (c*B-b*C)*Log[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/(e*(b^2-c^2)) + 
  Dist[(A*(b^2-c^2)-a*(b*B-c*C))/(b^2-c^2),Int[1/(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]),x]]) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[b^2-c^2] && NonzeroQ[A*(b^2-c^2)-a*(b*B-c*C)]

(* ::Code:: *)
Int[(A_.+C_.*Sinh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(32th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -c*C*x/(b^2-c^2) + b*C*Log[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/(e*(b^2-c^2)) + 
  Dist[(A*(b^2-c^2)+a*c*C)/(b^2-c^2),Int[1/(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]),x]]) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[b^2-c^2] && NonzeroQ[A*(b^2-c^2)+a*c*C]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_]),x_Symbol] :=
(Print["Int(33th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  b*B*x/(b^2-c^2) - c*B*Log[a+b*Cosh[d+e*x]+c*Sinh[d+e*x]]/(e*(b^2-c^2)) + 
  Dist[(A*(b^2-c^2)-a*b*B)/(b^2-c^2),Int[1/(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]),x]]) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2-c^2] && NonzeroQ[A*(b^2-c^2)-a*b*B]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_]+C_.*Sinh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^2,x_Symbol] :=
(Print["Int(34th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -(c*B-b*C-(a*C-c*A)*Cosh[d+e*x]+(b*A-a*B)*Sinh[d+e*x])/
    (e*(a^2-b^2+c^2)*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]))) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2+c^2] && ZeroQ[a*A-b*B+c*C]

(* ::Code:: *)
Int[(A_.+C_.*Sinh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^2,x_Symbol] :=
(Print["Int(35th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (b*C+(a*C-c*A)*Cosh[d+e*x]-b*A*Sinh[d+e*x])/(e*(a^2-b^2+c^2)*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]))) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2+c^2] && ZeroQ[a*A+c*C]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^2,x_Symbol] :=
(Print["Int(36th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -(c*B+c*A*Cosh[d+e*x]+(b*A-a*B)*Sinh[d+e*x])/(e*(a^2-b^2+c^2)*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]))) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2+c^2] && ZeroQ[a*A-b*B]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_]+C_.*Sinh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^2,x_Symbol] :=
(Print["Int(37th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -(c*B-b*C-(a*C-c*A)*Cosh[d+e*x]+(b*A-a*B)*Sinh[d+e*x])/
     (e*(a^2-b^2+c^2)*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])) +
  Dist[(a*A-b*B+c*C)/(a^2-b^2+c^2),Int[1/(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]),x]]) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2+c^2] && NonzeroQ[a*A-b*B+c*C]

(* ::Code:: *)
Int[(A_.+C_.*Sinh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^2,x_Symbol] :=
(Print["Int(38th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (b*C+(a*C-c*A)*Cosh[d+e*x]-b*A*Sinh[d+e*x])/(e*(a^2-b^2+c^2)*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])) +
  Dist[(a*A+c*C)/(a^2-b^2+c^2),Int[1/(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]),x]]) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2+c^2] && NonzeroQ[a*A+c*C]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_])/(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^2,x_Symbol] :=
(Print["Int(39th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -(c*B+c*A*Cosh[d+e*x]+(b*A-a*B)*Sinh[d+e*x])/(e*(a^2-b^2+c^2)*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])) +
  Dist[(a*A-b*B)/(a^2-b^2+c^2),Int[1/(a+b*Cosh[d+e*x]+c*Sinh[d+e*x]),x]]) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2+c^2] && NonzeroQ[a*A-b*B]

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_]+C_.*Sinh[d_.+e_.*x_])*(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(40th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  Dist[B/b,Int[(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1),x]] +
  Dist[(b*A-a*B)/b,Int[(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^n,x]]) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && ZeroQ[b*C-c*B] && NonzeroQ[b*A-a*B] && RationalQ[n] && (n==-1/2 || ZeroQ[a^2-b^2+c^2])

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_]+C_.*Sinh[d_.+e_.*x_])*(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(41th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (c*B-b*C-(a*C-c*A)*Cosh[d+e*x]+(b*A-a*B)*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2+c^2)) +
  Dist[1/((n+1)*(a^2-b^2+c^2)),
    Int[((n+1)*(a*A-b*B+c*C)-(n+2)*(b*A-a*B)*Cosh[d+e*x]+(n+2)*(a*C-c*A)*Sinh[d+e*x])*
      (a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2+c^2] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[(A_.+C_.*Sinh[d_.+e_.*x_])*(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(42th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  -(b*C+(a*C-c*A)*Cosh[d+e*x]-b*A*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2+c^2)) +
  Dist[1/((n+1)*(a^2-b^2+c^2)),
    Int[((n+1)*(a*A+c*C)-(n+2)*b*A*Cosh[d+e*x]+(n+2)*(a*C-c*A)*Sinh[d+e*x])*
      (a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2+c^2] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_])*(a_.+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(43th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (c*B+c*A*Cosh[d+e*x]+(b*A-a*B)*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2+c^2)) +
  Dist[1/((n+1)*(a^2-b^2+c^2)),
    Int[((n+1)*(a*A-b*B)-(n+2)*(b*A-a*B)*Cosh[d+e*x]-(n+2)*c*A*Sinh[d+e*x])*
      (a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2+c^2] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_]+C_.*Sinh[d_.+e_.*x_])*(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(44th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (-B*c+b*C+a*C*Cosh[d+e*x]+a*B*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^n/(a*e*(n+1)) + 
  Dist[1/(a*(n+1)),
    Int[(a*(b*B-c*C)*n + a^2*A*(n+1) + 
        (a^2*B*n - c*(b*C-c*B)*n + a*b*A*(n+1))*Cosh[d+e*x] + 
        (a^2*C*n - b*(b*C-c*B)*n + a*c*A*(n+1))*Sinh[d+e*x])*
      (a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n-1), x]]) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2+c^2] && RationalQ[n] && n>0

(* ::Code:: *)
Int[(A_.+C_.*Sinh[d_.+e_.*x_])*(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(45th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (b*C+a*C*Cosh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^n/(a*e*(n+1)) + 
  Dist[1/(a*(n+1)),
    Int[(-a*c*C*n+a^2*A*(n+1)-b*(c*C*n-a*A*(n+1))*Cosh[d+e*x]+(a^2*C*n-b^2*C*n+a*c*A*(n+1))*Sinh[d+e*x])*
      (a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n-1), x]]) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2+c^2] && RationalQ[n] && n>0

(* ::Code:: *)
Int[(A_.+B_.*Cosh[d_.+e_.*x_])*(a_+b_.*Cosh[d_.+e_.*x_]+c_.*Sinh[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(46th)@RationalFunctionsOfHyperbolicSinesAndCosines.m"];
  (-B*c+a*B*Sinh[d+e*x])*(a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^n/(a*e*(n+1)) + 
  Dist[1/(a*(n+1)),
    Int[(a*b*B*n+a^2*A*(n+1)+(a^2*B*n+c^2*B*n+a*b*A*(n+1))*Cosh[d+e*x]+c*(b*B*n+a*A*(n+1))*Sinh[d+e*x])*
      (a+b*Cosh[d+e*x]+c*Sinh[d+e*x])^(n-1), x]]) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2+c^2] && RationalQ[n] && n>0
