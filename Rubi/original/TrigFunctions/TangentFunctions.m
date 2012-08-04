(* ::Package:: *)

(* ::Code:: *)
Int[Tan[a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@TangentFunctions.m"];
  -Log[Cos[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Cot[a_.+b_.*x_],x_Symbol] :=
(Print["Int(2th)@TangentFunctions.m"];
  Log[Sin[a+b*x]]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Tan[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(3th)@TangentFunctions.m"];
  -x + Tan[a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Cot[a_.+b_.*x_]^2,x_Symbol] :=
(Print["Int(4th)@TangentFunctions.m"];
  -x - Cot[a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[(c_.*Tan[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(5th)@TangentFunctions.m"];
  c*(c*Tan[a+b*x])^(n-1)/(b*(n-1)) - 
  Dist[c^2,Int[(c*Tan[a+b*x])^(n-2),x]]) /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[(c_.*Cot[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(6th)@TangentFunctions.m"];
  -c*(c*Cot[a+b*x])^(n-1)/(b*(n-1)) - 
  Dist[c^2,Int[(c*Cot[a+b*x])^(n-2),x]]) /;
FreeQ[{a,b,c},x] && RationalQ[n] && n>1

(* ::Code:: *)
Int[(c_.*Tan[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(7th)@TangentFunctions.m"];
  (c*Tan[a+b*x])^(n+1)/(b*c*(n+1)) - 
  Dist[1/c^2,Int[(c*Tan[a+b*x])^(n+2),x]]) /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[(c_.*Cot[a_.+b_.*x_])^n_,x_Symbol] :=
(Print["Int(8th)@TangentFunctions.m"];
  -(c*Cot[a+b*x])^(n+1)/(b*c*(n+1)) - 
  Dist[1/c^2,Int[(c*Cot[a+b*x])^(n+2),x]]) /;
FreeQ[{a,b,c},x] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[1/(a_+b_.*Tan[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(9th)@TangentFunctions.m"];
  x/(2*a) - a/(2*b*d*(a+b*Tan[c+d*x]))) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]

(* ::Code:: *)
Int[1/(a_+b_.*Cot[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(10th)@TangentFunctions.m"];
  x/(2*a) + a/(2*b*d*(a+b*Cot[c+d*x]))) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2]

(* ::Code:: *)
Int[Sqrt[a_+b_.*Tan[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(11th)@TangentFunctions.m"];
  -Sqrt[2]*b*ArcTanh[Sqrt[a+b*Tan[c+d*x]]/(Sqrt[2]*Rt[a,2])]/(d*Rt[a,2])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && PosQ[a]

(* ::Code:: *)
Int[Sqrt[a_+b_.*Cot[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(12th)@TangentFunctions.m"];
  Sqrt[2]*b*ArcCoth[Sqrt[a+b*Cot[c+d*x]]/(Sqrt[2]*Rt[a,2])]/(d*Rt[a,2])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && PosQ[a]

(* ::Code:: *)
Int[Sqrt[a_+b_.*Tan[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(13th)@TangentFunctions.m"];
  Sqrt[2]*b*ArcTan[Sqrt[a+b*Tan[c+d*x]]/(Sqrt[2]*Rt[-a,2])]/(d*Rt[-a,2])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && NegQ[a]

(* ::Code:: *)
Int[Sqrt[a_+b_.*Cot[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(14th)@TangentFunctions.m"];
  Sqrt[2]*b*ArcCot[Sqrt[a+b*Cot[c+d*x]]/(Sqrt[2]*Rt[-a,2])]/(d*Rt[-a,2])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && NegQ[a]

(* ::Code:: *)
Int[(a_+b_.*Tan[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(15th)@TangentFunctions.m"];
  -a^2*(a+b*Tan[c+d*x])^(n-1)/(b*d*(n-1)) + 
  Dist[2*a,Int[(a+b*Tan[c+d*x])^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && FractionQ[n] && n>1

(* ::Code:: *)
Int[(a_+b_.*Cot[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(16th)@TangentFunctions.m"];
  a^2*(a+b*Cot[c+d*x])^(n-1)/(b*d*(n-1)) + 
  Dist[2*a,Int[(a+b*Cot[c+d*x])^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && FractionQ[n] && n>1

(* ::Code:: *)
Int[(a_+b_.*Tan[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(17th)@TangentFunctions.m"];
  a*(a+b*Tan[c+d*x])^n/(2*b*d*n) + 
  Dist[1/(2*a),Int[(a+b*Tan[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0

(* ::Code:: *)
Int[(a_+b_.*Cot[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(18th)@TangentFunctions.m"];
  -a*(a+b*Cot[c+d*x])^n/(2*b*d*n) + 
  Dist[1/(2*a),Int[(a+b*Cot[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2+b^2] && RationalQ[n] && n<0

(* ::Code:: *)
Int[1/(a_+b_.*Tan[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(19th)@TangentFunctions.m"];
  a*x/(a^2+b^2) + b*Log[a*Cos[c+d*x]+b*Sin[c+d*x]]/(d*(a^2+b^2))) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]

(* ::Code:: *)
Int[1/(a_+b_.*Cot[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(20th)@TangentFunctions.m"];
  a*x/(a^2+b^2) - b*Log[b*Cos[c+d*x]+a*Sin[c+d*x]]/(d*(a^2+b^2))) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]

(* ::Code:: *)
Int[Sqrt[a_+b_.*Tan[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(21th)@TangentFunctions.m"];
  Dist[(a-b*I)/2,Int[(1+I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x]] +
  Dist[(a+b*I)/2,Int[(1-I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]

(* ::Code:: *)
Int[Sqrt[a_+b_.*Cot[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(22th)@TangentFunctions.m"];
  Dist[(a-b*I)/2,Int[(1+I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x]] +
  Dist[(a+b*I)/2,Int[(1-I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*Tan[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(23th)@TangentFunctions.m"];
  Dist[1/2,Int[(1+I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x]] +
  Dist[1/2,Int[(1-I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*Cot[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(24th)@TangentFunctions.m"];
  Dist[1/2,Int[(1+I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x]] +
  Dist[1/2,Int[(1-I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]

(* ::Code:: *)
Int[(a_+b_.*Tan[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(25th)@TangentFunctions.m"];
  b*(a+b*Tan[c+d*x])^(n-1)/(d*(n-1)) + 
  Int[(a^2-b^2+2*a*b*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n-2),x]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && FractionQ[n] && n>1

(* ::Code:: *)
Int[(a_+b_.*Cot[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(26th)@TangentFunctions.m"];
  -b*(a+b*Cot[c+d*x])^(n-1)/(d*(n-1)) + 
  Int[(a^2-b^2+2*a*b*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n-2),x]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && FractionQ[n] && n>1

(* ::Code:: *)
Int[(a_+b_.*Tan[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(27th)@TangentFunctions.m"];
  (b*(a+b*Tan[c+d*x])^(n+1))/(d*(a^2+b^2)*(n+1)) + 
  Dist[1/(a^2+b^2),Int[(a-b*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[(a_+b_.*Cot[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(28th)@TangentFunctions.m"];
  -(b*(a+b*Cot[c+d*x])^(n+1))/(d*(a^2+b^2)*(n+1)) + 
  Dist[1/(a^2+b^2),Int[(a-b*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1

(* ::Code:: *)
Int[(A_.+B_.*Tan[c_.+d_.*x_])/(a_.+b_.*Tan[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(29th)@TangentFunctions.m"];
  B*x/b + Dist[(b*A-a*B)/b,Int[1/(a+b*Tan[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[b*A-a*B]

(* ::Code:: *)
Int[(A_.+B_.*Cot[c_.+d_.*x_])/(a_.+b_.*Cot[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(30th)@TangentFunctions.m"];
  B*x/b + Dist[(b*A-a*B)/b,Int[1/(a+b*Cot[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[b*A-a*B]

(* ::Code:: *)
Int[(A_+B_.*Tan[c_.+d_.*x_])/Sqrt[a_.+b_.*Tan[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(31th)@TangentFunctions.m"];
  -2*B*ArcTanh[Sqrt[a+b*Tan[c+d*x]]/Rt[a+b*A/B,2]]/(d*Rt[a+b*A/B,2])) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A^2+B^2] && NonzeroQ[b*A+a*B]

(* ::Code:: *)
Int[(A_+B_.*Cot[c_.+d_.*x_])/Sqrt[a_.+b_.*Cot[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(32th)@TangentFunctions.m"];
  2*B*ArcCoth[Sqrt[a+b*Cot[c+d*x]]/Rt[a+b*A/B,2]]/(d*Rt[a+b*A/B,2])) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[A^2+B^2] && NonzeroQ[b*A+a*B]

(* ::Code:: *)
Int[(A_.+B_.*Tan[c_.+d_.*x_])/Sqrt[a_.+b_.*Tan[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(33th)@TangentFunctions.m"];
  Dist[(A-B*I)/2,Int[(1+I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x]] +
  Dist[(A+B*I)/2,Int[(1-I*Tan[c+d*x])/Sqrt[a+b*Tan[c+d*x]],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A^2+B^2] && NonzeroQ[a^2+b^2]

(* ::Code:: *)
Int[(A_.+B_.*Cot[c_.+d_.*x_])/Sqrt[a_.+b_.*Cot[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(34th)@TangentFunctions.m"];
  Dist[(A-B*I)/2,Int[(1+I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x]] +
  Dist[(A+B*I)/2,Int[(1-I*Cot[c+d*x])/Sqrt[a+b*Cot[c+d*x]],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[A^2+B^2] && NonzeroQ[a^2+b^2]

(* ::Code:: *)
Int[(A_.+B_.*Tan[c_.+d_.*x_])*(a_+b_.*Tan[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(35th)@TangentFunctions.m"];
  B*(a+b*Tan[c+d*x])^n/(d*n) + 
  Dist[a*A-b*B,Int[(a+b*Tan[c+d*x])^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && FractionQ[n] && n>0 && ZeroQ[b*A+a*B]

(* ::Code:: *)
Int[(A_.+B_.*Cot[c_.+d_.*x_])*(a_+b_.*Cot[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(36th)@TangentFunctions.m"];
  -B*(a+b*Cot[c+d*x])^n/(d*n) + 
  Dist[a*A-b*B,Int[(a+b*Cot[c+d*x])^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && FractionQ[n] && n>0 && ZeroQ[b*A+a*B]

(* ::Code:: *)
Int[(A_.+B_.*Tan[c_.+d_.*x_])*(a_+b_.*Tan[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(37th)@TangentFunctions.m"];
  B*(a+b*Tan[c+d*x])^n/(d*n) + 
  Int[(a*A-b*B+(b*A+a*B)*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n-1),x]) /;
FreeQ[{a,b,c,d,A,B},x] && FractionQ[n] && n>0 && NonzeroQ[b*A+a*B]

(* ::Code:: *)
Int[(A_.+B_.*Cot[c_.+d_.*x_])*(a_+b_.*Cot[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(38th)@TangentFunctions.m"];
  -B*(a+b*Cot[c+d*x])^n/(d*n) + 
  Int[(a*A-b*B+(b*A+a*B)*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n-1),x]) /;
FreeQ[{a,b,c,d,A,B},x] && FractionQ[n] && n>0 && NonzeroQ[b*A+a*B]

(* ::Code:: *)
Int[(A_.+B_.*Tan[c_.+d_.*x_])*(a_+b_.*Tan[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(39th)@TangentFunctions.m"];
  (b*A-a*B)*(a+b*Tan[c+d*x])^(n+1)/(d*(a^2+b^2)*(n+1)) + 
  Dist[1/(a^2+b^2),Int[(a*A+b*B-(b*A-a*B)*Tan[c+d*x])*(a+b*Tan[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && NonzeroQ[b*A-a*B]

(* ::Code:: *)
Int[(A_.+B_.*Cot[c_.+d_.*x_])*(a_+b_.*Cot[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(40th)@TangentFunctions.m"];
  -(b*A-a*B)*(a+b*Cot[c+d*x])^(n+1)/(d*(a^2+b^2)*(n+1)) + 
  Dist[1/(a^2+b^2),Int[(a*A+b*B-(b*A-a*B)*Cot[c+d*x])*(a+b*Cot[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && NonzeroQ[b*A-a*B]

(* ::Code:: *)
Int[u_.*(a_+b_.*Tan[v_]^2)^m_,x_Symbol] :=
(Print["Int(41th)@TangentFunctions.m"];
  Dist[b^m,Int[u*Sec[v]^(2*m),x]]) /;
FreeQ[{a,b,m},x] && ZeroQ[a-b] && IntegerQ[m]

(* ::Code:: *)
Int[u_.*(a_+b_.*Cot[v_]^2)^m_,x_Symbol] :=
(Print["Int(42th)@TangentFunctions.m"];
  Dist[b^m,Int[u*Csc[v]^(2*m),x]]) /;
FreeQ[{a,b,m},x] && ZeroQ[a-b] && IntegerQ[m]

(* ::Code:: *)
Int[u_.*(a_+b_.*Tan[v_]^2)^m_,x_Symbol] :=
(Print["Int(43th)@TangentFunctions.m"];
  Int[u*(b*Sec[v]^2)^m,x]) /;
FreeQ[{a,b,m},x] && ZeroQ[a-b] && Not[IntegerQ[m]]

(* ::Code:: *)
Int[u_.*(a_+b_.*Cot[v_]^2)^m_,x_Symbol] :=
(Print["Int(44th)@TangentFunctions.m"];
  Int[u*(b*Csc[v]^2)^m,x]) /;
FreeQ[{a,b,m},x] && ZeroQ[a-b] && Not[IntegerQ[m]]

(* ::Code:: *)
Int[1/(a_+b_.*Tan[c_.+d_.*x_]^2),x_Symbol] :=
(Print["Int(45th)@TangentFunctions.m"];
  x/(a-b) - Sqrt[b]*ArcTan[Sqrt[b]*Tan[c+d*x]/Sqrt[a]]/(Sqrt[a]*d*(a-b))) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b]

(* ::Code:: *)
Int[1/(a_+b_.*Cot[c_.+d_.*x_]^2),x_Symbol] :=
(Print["Int(46th)@TangentFunctions.m"];
  x/(a-b) + Sqrt[b]*ArcTan[Sqrt[b]*Cot[c+d*x]/Sqrt[a]]/(Sqrt[a]*d*(a-b))) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a-b]

(* ::Code:: *)
Int[x_^m_.*Tan[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(47th)@TangentFunctions.m"];
  -I*x^(m+1)/(m+1) + 
  Dist[2*I,Int[x^m/(1+E^(2*I*a+2*I*b*x^n)),x]]) /;
FreeQ[{a,b,n},x] && IntegerQ[m] && m>0 && NonzeroQ[m-n+1] && n===1

(* ::Code:: *)
Int[x_^m_.*Cot[a_.+b_.*x_^n_.],x_Symbol] :=
(Print["Int(48th)@TangentFunctions.m"];
  I*x^(m+1)/(m+1) - 
  Dist[2*I,Int[x^m/(1-E^(2*I*a+2*I*b*x^n)),x]]) /;
FreeQ[{a,b,n},x] && IntegerQ[m] && m>0 && NonzeroQ[m-n+1] && n===1

(* ::Code:: *)
Int[x_^m_.*Tan[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(49th)@TangentFunctions.m"];
  x^(m-n+1)*Tan[a+b*x^n]^(p-1)/(b*n*(p-1)) - 
  Dist[(m-n+1)/(b*n*(p-1)),Int[x^(m-n)*Tan[a+b*x^n]^(p-1),x]] - 
  Int[x^m*Tan[a+b*x^n]^(p-2),x]) /;
FreeQ[{a,b},x] && RationalQ[{m,n,p}] && p>1 && NonzeroQ[m-n+1] && 0<n<=m

(* ::Code:: *)
Int[x_^m_.*Cot[a_.+b_.*x_^n_.]^p_,x_Symbol] :=
(Print["Int(50th)@TangentFunctions.m"];
  -x^(m-n+1)*Cot[a+b*x^n]^(p-1)/(b*n*(p-1)) + 
  Dist[(m-n+1)/(b*n*(p-1)),Int[x^(m-n)*Cot[a+b*x^n]^(p-1),x]] - 
  Int[x^m*Cot[a+b*x^n]^(p-2),x]) /;
FreeQ[{a,b},x] && RationalQ[{m,n,p}] && p>1 && NonzeroQ[m-n+1] && 0<n<=m

(* ::Code:: *)
Int[x_*Tan[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(51th)@TangentFunctions.m"];
  -Log[Cos[a+b*x+c*x^2]]/(2*c) -
  Dist[b/(2*c),Int[Tan[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c},x]

(* ::Code:: *)
Int[x_*Cot[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(52th)@TangentFunctions.m"];
  Log[Sin[a+b*x+c*x^2]]/(2*c) -
  Dist[b/(2*c),Int[Cot[a+b*x+c*x^2],x]]) /;
FreeQ[{a,b,c},x]

(* ::Code:: *)
(* Int[x_^m_*Tan[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(53th)@TangentFunctions.m"];
  -x^(m-1)*Log[Cos[a+b*x+c*x^2]]/(2*c) - 
  Dist[b/(2*c),Int[x^(m-1)*Tan[a+b*x+c*x^2],x]] + 
  Dist[(m-1)/(2*c),Int[x^(m-2)*Log[Cos[a+b*x+c*x^2]],x]]) /;
FreeQ[{a,b,c},x] && RationalQ[m] && m>1 *)

(* ::Code:: *)
(* Int[x_^m_*Cot[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(54th)@TangentFunctions.m"];
  x^(m-1)*Log[Sin[a+b*x+c*x^2]]/(2*c) -
  Dist[b/(2*c),Int[x^(m-1)*Cot[a+b*x+c*x^2],x]] -
  Dist[(m-1)/(2*c),Int[x^(m-2)*Log[Sin[a+b*x+c*x^2]],x]]) /;
FreeQ[{a,b,c},x] && RationalQ[m] && m>1*)

