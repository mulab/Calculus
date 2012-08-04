(* ::Package:: *)

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(1th)@AlgebraicFunctionsOfTrinomials.m"];
  (b+2*c*x)/Sqrt[a+b*x+c*x^2]*Int[1/(b+2*c*x),x]) /;
FreeQ[{a,b,c},x] && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[1/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(2th)@AlgebraicFunctionsOfTrinomials.m"];
  ArcSinh[(b+2*c*x)/(Rt[c,2]*Sqrt[4*a-b^2/c])]/Rt[c,2]) /;
FreeQ[{a,b,c},x] && PositiveQ[4*a-b^2/c] && PosQ[c]

(* ::Code:: *)
Int[1/Sqrt[a_.+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(3th)@AlgebraicFunctionsOfTrinomials.m"];
  -ArcSin[(b+2*c*x)/(Rt[-c,2]*Sqrt[4*a-b^2/c])]/Rt[-c,2]) /;
FreeQ[{a,b,c},x] && PositiveQ[4*a-b^2/c] && NegQ[c]

(* ::Code:: *)
Int[1/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(4th)@AlgebraicFunctionsOfTrinomials.m"];
  2*ArcTanh[Rt[c,2]*x/Sqrt[b*x+c*x^2]]/Rt[c,2]) /;
FreeQ[{b,c},x] && Not[PositiveQ[-b^2/c]] && PosQ[c]

(* ::Code:: *)
Int[1/Sqrt[b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(5th)@AlgebraicFunctionsOfTrinomials.m"];
  2*ArcTan[Rt[-c,2]*x/Sqrt[b*x+c*x^2]]/Rt[-c,2]) /;
FreeQ[{b,c},x] && Not[PositiveQ[-b^2/c]] && NegQ[c]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(6th)@AlgebraicFunctionsOfTrinomials.m"];
  ArcTanh[(b+2*c*x)/(2*Rt[c,2]*Sqrt[a+b*x+c*x^2])]/Rt[c,2]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && PosQ[c]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_+c_.*x_^2],x_Symbol] :=
(Print["Int(7th)@AlgebraicFunctionsOfTrinomials.m"];
  -ArcTan[(b+2*c*x)/(2*Rt[-c,2]*Sqrt[a+b*x+c*x^2])]/Rt[-c,2]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && NegQ[c]

(* ::Code:: *)
Int[(a_+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(8th)@AlgebraicFunctionsOfTrinomials.m"];
  (b+2*c*x)*(a+b*x+c*x^2)^n/(2*c*(2*n+1))) /;
FreeQ[{a,b,c,n},x] && ZeroQ[b^2-4*a*c] && NonzeroQ[2*n+1] && Not[IntegerQ[n]]

(* ::Code:: *)
Int[1/(a_.+b_.*x_+c_.*x_^2)^(3/2),x_Symbol] :=
(Print["Int(9th)@AlgebraicFunctionsOfTrinomials.m"];
  -2*(b+2*c*x)/((b^2-4*a*c)*Sqrt[a+b*x+c*x^2])) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(10th)@AlgebraicFunctionsOfTrinomials.m"];
  (b+2*c*x)*(a+b*x+c*x^2)^n/(2*c*(2*n+1)) -
  Dist[n*(b^2-4*a*c)/(2*c*(2*n+1)),Int[(a+b*x+c*x^2)^(n-1),x]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && FractionQ[n] && n>0

(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2)^n_,x_Symbol] :=
(Print["Int(11th)@AlgebraicFunctionsOfTrinomials.m"];
  (b+2*c*x)*(a+b*x+c*x^2)^(n+1)/((n+1)*(b^2-4*a*c)) -
  Dist[2*c*(2*n+3)/((n+1)*(b^2-4*a*c)),Int[(a+b*x+c*x^2)^(n+1),x]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c] && FractionQ[n] && n<-1

(* ::Code:: *)
(* Int[1/((d_+e_.*x_)*Sqrt[a_.+c_.*x_^2]),x_Symbol] :=
(Print["Int(12th)@AlgebraicFunctionsOfTrinomials.m"];
   e*Sqrt[a+c*x^2]/(c*d*(d+e*x))) /;
FreeQ[{a,c,d,e},x] && ZeroQ[c*d^2+a*e^2] *)

(* ::Code:: *)
Int[1/((d_+e_.*x_)*Sqrt[a_.+c_.*x_^2]),x_Symbol] :=
(Print["Int(13th)@AlgebraicFunctionsOfTrinomials.m"];
  -ArcTanh[(a*e-c*d*x)/(Rt[c*d^2+a*e^2,2]*Sqrt[a+c*x^2])]/Rt[c*d^2+a*e^2,2]) /;
FreeQ[{a,c,d,e},x] && PosQ[c*d^2+a*e^2]

(* ::Code:: *)
Int[1/((d_+e_.*x_)*Sqrt[a_.+c_.*x_^2]),x_Symbol] :=
(Print["Int(14th)@AlgebraicFunctionsOfTrinomials.m"];
  ArcTan[(a*e-c*d*x)/(Rt[-c*d^2-a*e^2,2]*Sqrt[a+c*x^2])]/Rt[-c*d^2-a*e^2,2]) /;
FreeQ[{a,c,d,e},x] && NegQ[c*d^2+a*e^2]

(* ::Code:: *)
Int[1/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
(Print["Int(15th)@AlgebraicFunctionsOfTrinomials.m"];
  2*e*Sqrt[a+b*x+c*x^2]/((2*c*d-b*e)*(d+e*x))) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[c*d^2-b*d*e+a*e^2] && NonzeroQ[2*c*d-b*e]

(* ::Code:: *)
Int[1/((d_.+e_.*x_)*Sqrt[a_+b_.*x_+c_.*x_^2]),x_Symbol] :=
(Print["Int(16th)@AlgebraicFunctionsOfTrinomials.m"];
  (b+2*c*x)/Sqrt[a+b*x+c*x^2]*Int[1/((d+e*x)*(b+2*c*x)),x]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[1/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
(Print["Int(17th)@AlgebraicFunctionsOfTrinomials.m"];
  2/(e*Rt[(b^2-4*a*c)/c,2])*ArcTan[2*Sqrt[a+b*x+c*x^2]/Rt[(b^2-4*a*c)/c,2]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[2*c*d-b*e] && PosQ[(b^2-4*a*c)/c]

(* ::Code:: *)
Int[1/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
(Print["Int(18th)@AlgebraicFunctionsOfTrinomials.m"];
  -2/(e*Rt[(4*a*c-b^2)/c,2])*ArcTanh[2*Sqrt[a+b*x+c*x^2]/Rt[(4*a*c-b^2)/c,2]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[2*c*d-b*e] && NegQ[(b^2-4*a*c)/c]

(* ::Code:: *)
Int[1/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
(Print["Int(19th)@AlgebraicFunctionsOfTrinomials.m"];
  -1/Rt[c*d^2-b*d*e+a*e^2,2]*
  ArcTanh[(2*a*e-b*d-(2*c*d-b*e)*x)/(2*Rt[c*d^2-b*d*e+a*e^2,2]*Sqrt[a+b*x+c*x^2])]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && PosQ[c*d^2-b*d*e+a*e^2]

(* ::Code:: *)
Int[1/((d_.+e_.*x_)*Sqrt[a_.+b_.*x_+c_.*x_^2]),x_Symbol] :=
(Print["Int(20th)@AlgebraicFunctionsOfTrinomials.m"];
  1/Rt[-c*d^2+b*d*e-a*e^2,2]*
  ArcTan[(2*a*e-b*d-(2*c*d-b*e)*x)/(2*Rt[-c*d^2+b*d*e-a*e^2,2]*Sqrt[a+b*x+c*x^2])]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && NonzeroQ[2*c*d-b*e] && NegQ[c*d^2-b*d*e+a*e^2]

(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2)^n_/(d_.+e_.*x_),x_Symbol] :=
(Print["Int(21th)@AlgebraicFunctionsOfTrinomials.m"];
  (a+b*x+c*x^2)^n/(2*e*n) -
  Dist[(2*c*d-b*e)/(2*e^2),Int[(a+b*x+c*x^2)^(n-1),x]]) /;
FreeQ[{a,b,c,d,e},x] && FractionQ[n] && n>0 && ZeroQ[c*d^2-b*d*e+a*e^2]

(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2)^n_/(d_.+e_.*x_),x_Symbol] :=
(Print["Int(22th)@AlgebraicFunctionsOfTrinomials.m"];
  (a+b*x+c*x^2)^n/(2*e*n) +
  Dist[(c*d^2-b*d*e+a*e^2)/e^2,Int[(a+b*x+c*x^2)^(n-1)/(d+e*x),x]]) /;
FreeQ[{a,b,c,d,e},x] && FractionQ[n] && n>0 && ZeroQ[2*c*d-b*e]

(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2)^n_/(d_.+e_.*x_),x_Symbol] :=
(Print["Int(23th)@AlgebraicFunctionsOfTrinomials.m"];
  (a+b*x+c*x^2)^n/(2*e*n) -
  Dist[(2*c*d-b*e)/(2*e^2), Int[(a+b*x+c*x^2)^(n-1),x]] +
  Dist[(c*d^2-b*d*e+a*e^2)/e^2,Int[(a+b*x+c*x^2)^(n-1)/(d+e*x),x]]) /;
FreeQ[{a,b,c,d,e},x] && FractionQ[n] && n>0

(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2)^n_/(d_.+e_.*x_),x_Symbol] :=
(Print["Int(24th)@AlgebraicFunctionsOfTrinomials.m"];
  -e*(a+b*x+c*x^2)^(n+1)/(2*(n+1)*(c*d^2-b*d*e+a*e^2)) +
  Dist[e^2/(c*d^2-b*d*e+a*e^2),Int[(a+b*x+c*x^2)^(n+1)/(d+e*x),x]]) /;
FreeQ[{a,b,c,d,e},x] && FractionQ[n] && n<-1 && NonzeroQ[c*d^2-b*d*e+a*e^2] && ZeroQ[2*c*d-b*e]

(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2)^n_/(d_.+e_.*x_),x_Symbol] :=
(Print["Int(25th)@AlgebraicFunctionsOfTrinomials.m"];
  -e*(a+b*x+c*x^2)^(n+1)/(2*(n+1)*(c*d^2-b*d*e+a*e^2)) +
  Dist[(2*c*d-b*e)/(2*(c*d^2-b*d*e+a*e^2)), Int[(a+b*x+c*x^2)^n,x]] +
  Dist[e^2/(c*d^2-b*d*e+a*e^2),Int[(a+b*x+c*x^2)^(n+1)/(d+e*x),x]]) /;
FreeQ[{a,b,c,d,e},x] && FractionQ[n] && n<-1 && NonzeroQ[c*d^2-b*d*e+a*e^2]

(* ::Code:: *)
Int[1/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
(Print["Int(26th)@AlgebraicFunctionsOfTrinomials.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
  Int[1/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]]) /;
FreeQ[{a,b,c},x] && NonzeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(d_.+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
(Print["Int(27th)@AlgebraicFunctionsOfTrinomials.m"];
  Dist[(b+2*c*x^2)/Sqrt[a+b*x^2+c*x^4],Int[(d+e*x^2)/(b+2*c*x^2),x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(d_.+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
(Print["Int(28th)@AlgebraicFunctionsOfTrinomials.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Dist[1/Sqrt[a],Int[(d+e*x^2)/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c] && PositiveQ[a]

(* ::Code:: *)
Int[(d_.+e_.*x_^2)/Sqrt[a_+b_.*x_^2+c_.*x_^4],x_Symbol] :=
(Print["Int(29th)@AlgebraicFunctionsOfTrinomials.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]/Sqrt[a+b*x^2+c*x^4]*
  Int[(d+e*x^2)/(Sqrt[1+2*c*x^2/(b-q)]*Sqrt[1+2*c*x^2/(b+q)]),x]]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[1/(x_*Sqrt[b_.*x_^n_.+c_.*x_^j_.]),x_Symbol] :=
(Print["Int(30th)@AlgebraicFunctionsOfTrinomials.m"];
  -2*Sqrt[b*x^n+c*x^j]/(b*n*x^n)) /;
FreeQ[{b,c,n},x] && ZeroQ[j-2*n]

(* ::Code:: *)
Int[1/(x_*Sqrt[a_+b_.*x_^n_.+c_.*x_^j_.]),x_Symbol] :=
(Print["Int(31th)@AlgebraicFunctionsOfTrinomials.m"];
  -ArcTanh[(2*a+b*x^n)/(2*Rt[a,2]*Sqrt[a+b*x^n+c*x^j])]/(n*Rt[a,2])) /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && PosQ[a]

(* ::Code:: *)
Int[1/(x_*Sqrt[a_+b_.*x_^n_.+c_.*x_^j_.]),x_Symbol] :=
(Print["Int(32th)@AlgebraicFunctionsOfTrinomials.m"];
  ArcTan[(2*a+b*x^n)/(2*Rt[-a,2]*Sqrt[a+b*x^n+c*x^j])]/(n*Rt[-a,2])) /;
FreeQ[{a,b,c,n},x] && ZeroQ[j-2*n] && NonzeroQ[b^2-4*a*c] && NegQ[a]

(* ::Code:: *)
Int[(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(33th)@AlgebraicFunctionsOfTrinomials.m"];
  Sqrt[a+b*x^n+c*x^(2*n)]/(b+2*c*x^n)*Dist[1/(4*c)^(p-1/2),Int[(b+2*c*x^n)^(2*p),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegersQ[n,p-1/2] && n>1 && p>0 && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(34th)@AlgebraicFunctionsOfTrinomials.m"];
  (b+2*c*x^n)/Sqrt[a+b*x^n+c*x^(2*n)]*Dist[1/(4*c)^(p+1/2),Int[(b+2*c*x^n)^(2*p),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegersQ[n,p+1/2] && n>1 && p<0 && ZeroQ[b^2-4*a*c]

(* ::Code:: *)
Int[(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(35th)@AlgebraicFunctionsOfTrinomials.m"];
  x*(a+b*x^n+c*x^(2*n))^p/(2*n*p+1) +
  Dist[n*p/(2*n*p+1),Int[(2*a+b*x^n)*(a+b*x^n+c*x^(2*n))^(p-1),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegerQ[n] && n>1 && FractionQ[p] && p>0 && 
NonzeroQ[b^2-4*a*c] && NonzeroQ[2*n*p+1]

(* ::Code:: *)
Int[(b_.*x_+c_.*x_^2)^p_/x_,x_Symbol] :=
(Print["Int(36th)@AlgebraicFunctionsOfTrinomials.m"];
  (b*x+c*x^2)^(p+1)/(b*p*x) -
  Dist[c*(2*p+1)/(b*p),Int[(b*x+c*x^2)^p,x]]) /;
FreeQ[{b,c},x] && FractionQ[p] && p<-1/2

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_.+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(37th)@AlgebraicFunctionsOfTrinomials.m"];
  Sqrt[a+b*x^n+c*x^(2*n)]/(b+2*c*x^n)*Dist[1/(4*c)^(p-1/2),Int[x^m*(b+2*c*x^n)^(2*p),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegersQ[m,n,p-1/2] && n>0 && p>0 && ZeroQ[b^2-4*a*c] &&
NonzeroQ[m-n+1]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_.+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(38th)@AlgebraicFunctionsOfTrinomials.m"];
  (b+2*c*x^n)/Sqrt[a+b*x^n+c*x^(2*n)]*Dist[1/(4*c)^(p+1/2),Int[x^m*(b+2*c*x^n)^(2*p),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegersQ[m,n,p+1/2] && n>0 && p<0 && ZeroQ[b^2-4*a*c] &&
NonzeroQ[m-n+1]

(* ::Code:: *)
Int[x_^m_*(a_.+b_.*x_+c_.*x_^2)^p_,x_Symbol] :=
(Print["Int(39th)@AlgebraicFunctionsOfTrinomials.m"];
  -x^(m-1)*(a+b*x+c*x^2)^(p+1)/(c*(m-1)) -
  Dist[b/(2*c),Int[x^(m-1)*(a+b*x+c*x^2)^p,x]] +
  Dist[1/c,Int[x^(m-2)*(a+b*x+c*x^2)^(p+1),x]]) /;
FreeQ[{a,b,c},x] && IntegerQ[m] && FractionQ[p] && p<-1 && ZeroQ[m+2*p+1]

(* ::Code:: *)
Int[x_^m_*(a_+b_.*x_^n_.+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(40th)@AlgebraicFunctionsOfTrinomials.m"];
  x^(m+1)*(a+b*x^n+c*x^(2*n))^p/(m+1) -
  Dist[b*n*p/(m+1),Int[x^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1),x]] -
  Dist[2*c*n*p/(m+1),Int[x^(m+2*n)*(a+b*x^n+c*x^(2*n))^(p-1),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegersQ[m,n] && m<-1 && n>0 && FractionQ[p] && p>0

(* ::Code:: *)
(* Int[x_^m_*(a_+b_.*x_^n_.+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(41th)@AlgebraicFunctionsOfTrinomials.m"];
  x^(m+1)*(a+b*x^n+c*x^(2*n))^p/(m+2*n*p+1) +
  Dist[2*a*n*p/(m+2*n*p+1),Int[x^m*(a+b*x^n+c*x^(2*n))^(p-1),x]] +
  Dist[b*n*p/(m+2*n*p+1),Int[x^(m+n)*(a+b*x^n+c*x^(2*n))^(p-1),x]]) /;
FreeQ[{a,b,c},x] && ZeroQ[j-2*n] && IntegersQ[m,n] && m<-1 && n>0 && FractionQ[p] && p>0 &&
NonzeroQ[m+2*n*p+1] *)

(* ::Code:: *)
Int[x_^m_*(a_+b_.*x_^n_.+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(42th)@AlgebraicFunctionsOfTrinomials.m"];
  x^(m+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(a*(m+1)) -
  Dist[b*(m+n*(p+1)+1)/(a*(m+1)),Int[x^(m+n)*(a+b*x^n+c*x^(2*n))^p,x]] -
  Dist[c*(m+2*n*(p+1)+1)/(a*(m+1)),Int[x^(m+2*n)*(a+b*x^n+c*x^(2*n))^p,x]]) /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && IntegersQ[m,n] && m<-1 && n>0 && FractionQ[p] &&
NonzeroQ[m+n*(p+1)+1] && NonzeroQ[m+2*n*(p+1)+1]

(* ::Code:: *)
Int[x_^m_*(a_+b_.*x_^n_.+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(43th)@AlgebraicFunctionsOfTrinomials.m"];
  x^(m-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*n*(p+1)) +
  Dist[a/c,Int[x^(m-2*n)*(a+b*x^n+c*x^(2*n))^p,x]]) /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && IntegersQ[m,n] && 0<2*n<=m && FractionQ[p] &&
ZeroQ[m+n*(p-1)+1]

(* ::Code:: *)
Int[x_^m_*(a_+b_.*x_^n_.+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(44th)@AlgebraicFunctionsOfTrinomials.m"];
  x^(m-2*n+1)*(a+b*x^n+c*x^(2*n))^(p+1)/(c*(m+2*n*p+1)) -
  Dist[b*(m+n*(p-1)+1)/(c*(m+2*n*p+1)),Int[x^(m-n)*(a+b*x^n+c*x^(2*n))^p,x]] -
  Dist[a*(m-2*n+1)/(c*(m+2*n*p+1)),Int[x^(m-2*n)*(a+b*x^n+c*x^(2*n))^p,x]]) /;
FreeQ[{a,b,c,p},x] && ZeroQ[j-2*n] && IntegersQ[m,n] && 0<2*n<=m && FractionQ[p] &&
NonzeroQ[m+2*n*p+1] && NonzeroQ[m+n*(p-1)+1]

(* ::Code:: *)
Int[(d_.+e_.*x_^n_)*(a_+b_.*x_^n_+c_.*x_^j_)^p_,x_Symbol] :=
(Print["Int(45th)@AlgebraicFunctionsOfTrinomials.m"];
  x*(b*e*n*p+c*d*(2*n*p+n+1)+c*e*(2*n*p+1)*x^n)*(a+b*x^n+c*x^(2*n))^p/(c*(2*n*p+1)*(2*n*p+n+1)) -
  Dist[n*p/(c*(2*n*p+1)*(2*n*p+n+1)),
    Int[(a*b*e-2*a*c*d*(2*n*p+n+1)-(2*a*c*e*(2*n*p+1)+b*c*d*(2*n*p+n+1)-b^2*e*(n*p+1))*x^n)*
      (a+b*x^n+c*x^(2*n))^(p-1),x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[j-2*n] && IntegerQ[n] && n>1 && FractionQ[p] && p>0 && 
NonzeroQ[b^2-4*a*c] && NonzeroQ[2*n*p+1] && NonzeroQ[2*n*p+n+1] 

(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
(Print["Int(46th)@AlgebraicFunctionsOfTrinomials.m"];
  Subst[Int[(a+5*d^4/(256*e^3)-c*d^2/(16*e^2)+(c-3*d^2/(8*e))*x^2+e*x^4)^p,x],x,d/(4*e)+x]) /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p-1/2] && ZeroQ[d^3-4*c*d*e+8*b*e^2]

(* ::Code:: *)
Int[(a_.+b_.*x_+c_.*x_^2+d_.*x_^3+e_.*x_^4)^p_,x_Symbol] :=
(Print["Int(47th)@AlgebraicFunctionsOfTrinomials.m"];
  Dist[-16*a^2,Subst[
    Int[(a*(-3*b^4+16*a*b^2*c-64*a^2*b*d+256*a^3*e-32*a^2*(3*b^2-8*a*c)*x^2+256*a^4*x^4)/(b-4*a*x)^4)^p/(b-4*a*x)^2,x],x,b/(4*a)+1/x]]) /;
FreeQ[{a,b,c,d,e},x] && IntegerQ[p-1/2] && ZeroQ[b^3-4*a*b*c+8*a^2*d]

(* ::Code:: *)
Int[u_^p_,x_Symbol] :=
(Print["Int(48th)@AlgebraicFunctionsOfTrinomials.m"];
  Module[{v=Expand[u,x]},
  Int[v^p,x] /;
 v=!=u && (
 MatchQ[v,a_+b_.*x^2+c_.*x^4 /; FreeQ[{a,b,c},x]] ||
 MatchQ[v,a_.+b_.*x+c_.*x^2+d_.*x^3+e_.*x^4 /; FreeQ[{a,b,c,d,e},x] && ZeroQ[d^3-4*c*d*e+8*b*e^2]])]) /;
PolynomialQ[u,x] && Exponent[u,x]==4 && IntegerQ[p-1/2]
