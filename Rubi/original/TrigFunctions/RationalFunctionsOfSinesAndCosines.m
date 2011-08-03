(* ::Package:: *)

(************************************************************************)
(* This file was generated automatically by the Mathematica front end.  *)
(* It contains Initialization cells from a Notebook file, which         *)
(* typically will have the same name as this file except ending in      *)
(* ".nb" instead of ".m".                                               *)
(*                                                                      *)
(* This file is intended to be loaded into the Mathematica kernel using *)
(* the package loading commands Get or Needs.  Doing so is equivalent   *)
(* to using the Evaluate Initialization Cells menu command in the front *)
(* end.                                                                 *)
(*                                                                      *)
(* DO NOT EDIT THIS FILE.  This entire file is regenerated              *)
(* automatically each time the parent Notebook file is saved in the     *)
(* Mathematica front end.  Any changes you make to this file will be    *)
(* overwritten.                                                         *)
(************************************************************************)



(* ::Code:: *)
Int[Sqrt[a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
  Dist[(a^2+b^2)^(1/4),Int[Sqrt[Cos[c+d*x-ArcTan[a,b]]],x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && PositiveQ[Sqrt[a^2+b^2]]


(* ::Code:: *)
(* Int[Sqrt[a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[a*Cos[c+d*x]+b*Sin[c+d*x]]/Sqrt[(a*Cos[c+d*x]+b*Sin[c+d*x])/Sqrt[a^2+b^2]]*
    Int[Sqrt[Cos[c+d*x-ArcTan[a,b]]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && Not[PositiveQ[Sqrt[a^2+b^2]]] *)


(* ::Code:: *)
Int[1/Sqrt[a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
  Dist[1/(a^2+b^2)^(1/4),Int[1/Sqrt[Cos[c+d*x-ArcTan[a,b]]],x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && PositiveQ[Sqrt[a^2+b^2]]


(* ::Code:: *)
(* Int[1/Sqrt[a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
  Sqrt[(a*Cos[c+d*x]+b*Sin[c+d*x])/Sqrt[a^2+b^2]]/Sqrt[a*Cos[c+d*x]+b*Sin[c+d*x]]*
    Int[1/Sqrt[Cos[c+d*x-ArcTan[a,b]]],x] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && Not[PositiveQ[Sqrt[a^2+b^2]]] *)


(* ::Code:: *)
Int[(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
  a*(a*Cos[c+d*x]+b*Sin[c+d*x])^n/(b*d*n) /;
FreeQ[{a,b,c,d,n},x] && ZeroQ[a^2+b^2]


(* ::Code:: *)
Int[1/(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_])^2,x_Symbol] :=
  Sin[c+d*x]/(a*d*(a*Cos[c+d*x]+b*Sin[c+d*x])) /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2]


(* ::Code:: *)
Int[(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
  Dist[1/d,Subst[Int[Regularize[(a^2+b^2-x^2)^((n-1)/2),x],x],x,-b*Cos[c+d*x]+a*Sin[c+d*x]]] /;
FreeQ[{a,b},x] && NonzeroQ[a^2+b^2] && OddQ[n] && n>0


(* ::Code:: *)
Int[(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
  -(b*Cos[c+d*x]-a*Sin[c+d*x])*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-1)/(d*n) +
  Dist[(n-1)*(a^2+b^2)/n,Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n-2),x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n>1 && Not[OddQ[n]]


(* ::Code:: *)
Int[(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
  (b*Cos[c+d*x]-a*Sin[c+d*x])*(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2+b^2)) +
  Dist[(n+2)/((n+1)*(a^2+b^2)),Int[(a*Cos[c+d*x]+b*Sin[c+d*x])^(n+2),x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && RationalQ[n] && n<-1 && n!=-2


(* ::Code:: *)
(* Int[Cos[c_.+d_.*x_]^m_.*Sin[c_.+d_.*x_]^n_./(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  Dist[b/(a^2+b^2),Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-1),x]] +
  Dist[a/(a^2+b^2),Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^n,x]] -
  Dist[a*b/(a^2+b^2),Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^(n-1)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && IntegersQ[m,n] && m>0 && n>0 *)


(* ::Code:: *)
Int[Cos[c_.+d_.*x_]^m_.*Sin[c_.+d_.*x_]^n_.*(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_])^p_,x_Symbol] :=
  Dist[b/(a^2+b^2),Int[Cos[c+d*x]^m*Sin[c+d*x]^(n-1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^(p+1),x]] +
  Dist[a/(a^2+b^2),Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^n*(a*Cos[c+d*x]+b*Sin[c+d*x])^(p+1),x]] -
  Dist[a*b/(a^2+b^2),Int[Cos[c+d*x]^(m-1)*Sin[c+d*x]^(n-1)*(a*Cos[c+d*x]+b*Sin[c+d*x])^p,x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && IntegersQ[m,n,p] && m>0 && n>0 && p<0


(* ::Code:: *)
Int[u_.*Sin[c_.+d_.*x_]^n_./(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  Dist[b/(a^2+b^2),Int[u*Sin[c+d*x]^(n-1),x]] -
  Dist[a/(a^2+b^2),Int[u*Sin[c+d*x]^(n-2)*Cos[c+d*x],x]] +
  Dist[a^2/(a^2+b^2),Int[u*Sin[c+d*x]^(n-2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && IntegerQ[n] && n>0 &&
(n>1 || MatchQ[u,v_.*Tan[c+d*x]^m_. /; IntegerQ[m] && m>0])


(* ::Code:: *)
Int[u_.*Cos[c_.+d_.*x_]^n_./(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  Dist[a/(a^2+b^2),Int[u*Cos[c+d*x]^(n-1),x]] -
  Dist[b/(a^2+b^2),Int[u*Cos[c+d*x]^(n-2)*Sin[c+d*x],x]] +
  Dist[b^2/(a^2+b^2),Int[u*Cos[c+d*x]^(n-2)/(a*Cos[c+d*x]+b*Sin[c+d*x]),x]] /;
FreeQ[{a,b,c,d},x] && NonzeroQ[a^2+b^2] && IntegerQ[n] && n>0 &&
(n>1 || MatchQ[u,v_.*Cot[c+d*x]^m_. /; IntegerQ[m] && m>0])


(* ::Code:: *)
(* Int[u_.*Sec[c_.+d_.*x_]/(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  Dist[1/b,Int[u*Tan[c+d*x],x]] + 
  Dist[1/b,Int[u*(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x]] /;
FreeQ[{a,b,c,d},x] *)


(* ::Code:: *)
(* Int[u_.*Csc[c_.+d_.*x_]/(a_.*Cos[c_.+d_.*x_]+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
  Dist[1/a,Int[u*Cot[c+d*x],x]] - 
  Dist[1/a,Int[u*(b*Cos[c+d*x]-a*Sin[c+d*x])/(a*Cos[c+d*x]+b*Sin[c+d*x]),x]] /;
FreeQ[{a,b,c,d},x] *)


(* ::Code:: *)
Int[1/(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  Log[a+c*Tan[(d+e*x)/2]]/(c*e) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a-b]


(* ::Code:: *)
Int[1/(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  -Log[a+c*Cot[(d+e*x)/2]]/(c*e) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a+b]


(* ::Code:: *)
Int[1/(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  (-c+a*Sin[d+e*x])/(c*e*(c*Cos[d+e*x]-b*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2]


(* ::Code:: *)
Int[1/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  2*ArcTan[(c+(a-b)*Tan[(d+e*x)/2])/Rt[a^2-b^2-c^2,2]]/(e*Rt[a^2-b^2-c^2,2]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2] && PosQ[a^2-b^2-c^2]


(* ::Code:: *)
Int[1/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  -2*ArcTanh[(c+(a-b)*Tan[(d+e*x)/2])/Rt[-a^2+b^2+c^2,2]]/(e*Rt[-a^2+b^2+c^2,2]) /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2] && NegQ[a^2-b^2-c^2]


(* ::Code:: *)
Int[Sqrt[a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]],x_Symbol] :=
  2*(-c*Cos[d+e*x]+b*Sin[d+e*x])/(e*Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2]


(* ::Code:: *)
Int[Sqrt[a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]],x_Symbol] :=
  Int[Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2] && PositiveQ[a+Sqrt[b^2+c^2]]


(* ::Code:: *)
Int[Sqrt[a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]],x_Symbol] :=
  Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/Sqrt[(a+b*Cos[d+e*x]+c*Sin[d+e*x])/(a+Sqrt[b^2+c^2])]*
    Int[Sqrt[a/(a+Sqrt[b^2+c^2])+Sqrt[b^2+c^2]/(a+Sqrt[b^2+c^2])*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2] && Not[PositiveQ[a+Sqrt[b^2+c^2]]]


(* ::Code:: *)
Int[1/Sqrt[a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]],x_Symbol] :=
  Int[1/Sqrt[a+Sqrt[b^2+c^2]*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && PositiveQ[a+Sqrt[b^2+c^2]]


(* ::Code:: *)
Int[1/Sqrt[a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]],x_Symbol] :=
  Sqrt[(a+b*Cos[d+e*x]+c*Sin[d+e*x])/(a+Sqrt[b^2+c^2])]/Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]*
    Int[1/Sqrt[a/(a+Sqrt[b^2+c^2])+Sqrt[b^2+c^2]/(a+Sqrt[b^2+c^2])*Cos[d+e*x-ArcTan[b,c]]],x] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a+Sqrt[b^2+c^2]] && Not[PositiveQ[a+Sqrt[b^2+c^2]]]


(* ::Code:: *)
Int[(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (-c*Cos[d+e*x]+b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)/(e*n) +
  Dist[a*(2*n-1)/n,Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1),x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2] && RationalQ[n] && n>1


(* ::Code:: *)
Int[(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (-c*Cos[d+e*x]+b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1)/(e*n) +
  Dist[1/n,Int[(n*a^2+(n-1)*(b^2+c^2)+a*b*(2*n-1)*Cos[d+e*x]+a*c*(2*n-1)*Sin[d+e*x])*
    (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-2),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2] && FractionQ[n] && n>1


(* ::Code:: *)
Int[(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (c*Cos[d+e*x]-b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(2*n+1)) +
  Dist[(n+1)/(a*(2*n+1)),Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x]] /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2] && RationalQ[n] && n<-1


(* ::Code:: *)
Int[1/(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*Cos[d+e*x]-b*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  Dist[a/(a^2-b^2-c^2),Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2]


(* ::Code:: *)
Int[1/(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^(3/2),x_Symbol] :=
  2*(c*Cos[d+e*x]-b*Sin[d+e*x])/(e*(a^2-b^2-c^2)*Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]) +
  Dist[1/(a^2-b^2-c^2),Int[Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]],x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2]


(* ::Code:: *)
Int[(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (-c*Cos[d+e*x]+b*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/(e*(n+1)*(a^2-b^2-c^2)) +
  Dist[1/((n+1)*(a^2-b^2-c^2)),
    Int[((n+1)*a-(n+2)*b*Cos[d+e*x]-(n+2)*c*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x]] /;
FreeQ[{a,b,c,d,e},x] && NonzeroQ[a^2-b^2-c^2] && RationalQ[n] && n<-1 && n!=-2 && n!=-3/2


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_]+C_.*Sin[d_.+e_.*x_])/(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  (2*a*A-b*B-c*C)*x/(2*a^2) - (b*B+c*C)*(b*Cos[d+e*x]-c*Sin[d+e*x])/(2*a*b*c*e) + 
  (a^2*(b*B-c*C)-2*a*A*b^2+b^2*(b*B+c*C))*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(2*a^2*b*c*e) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && ZeroQ[b^2+c^2]


(* ::Code:: *)
Int[(A_.+C_.*Sin[d_.+e_.*x_])/(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  (2*a*A-c*C)*x/(2*a^2) - C*Cos[d+e*x]/(2*a*e) + c*C*Sin[d+e*x]/(2*a*b*e) + 
  (-a^2*C+2*a*c*A+b^2*C)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(2*a^2*b*e) /;
FreeQ[{a,b,c,d,e,A,C},x] && ZeroQ[b^2+c^2]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_])/(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  (2*a*A-b*B)*x/(2*a^2) - b*B*Cos[d+e*x]/(2*a*c*e) + B*Sin[d+e*x]/(2*a*e) + 
  (a^2*B-2*a*b*A+b^2*B)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(2*a^2*c*e) /;
FreeQ[{a,b,c,d,e,A,B},x] && ZeroQ[b^2+c^2]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_]+C_.*Sin[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  (b*B+c*C)*x/(b^2+c^2) + (c*B-b*C)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[b^2+c^2] && ZeroQ[A*(b^2+c^2)-a*(b*B+c*C)]


(* ::Code:: *)
Int[(A_.+C_.*Sin[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  c*C*x/(b^2+c^2) - b*C*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[b^2+c^2] && ZeroQ[A*(b^2+c^2)-a*c*C]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  b*B*x/(b^2+c^2) + c*B*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2+c^2] && ZeroQ[A*(b^2+c^2)-a*b*B]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_]+C_.*Sin[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  (b*B+c*C)*x/(b^2+c^2) + (c*B-b*C)*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
  Dist[(A*(b^2+c^2)-a*(b*B+c*C))/(b^2+c^2),Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[b^2+c^2] && NonzeroQ[A*(b^2+c^2)-a*(b*B+c*C)]


(* ::Code:: *)
Int[(A_.+C_.*Sin[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  c*C*(d+e*x)/(e*(b^2+c^2)) - b*C*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
  Dist[(A*(b^2+c^2)-a*c*C)/(b^2+c^2),Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[b^2+c^2] && NonzeroQ[A*(b^2+c^2)-a*c*C]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_]),x_Symbol] :=
  b*B*(d+e*x)/(e*(b^2+c^2)) +
  c*B*Log[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(e*(b^2+c^2)) +
  Dist[(A*(b^2+c^2)-a*b*B)/(b^2+c^2),Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[b^2+c^2] && NonzeroQ[A*(b^2+c^2)-a*b*B]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_]+C_.*Sin[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/
    (e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2-c^2] && ZeroQ[a*A-b*B-c*C]


(* ::Code:: *)
Int[(A_.+C_.*Sin[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^2,x_Symbol] :=
  -(b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2-c^2] && ZeroQ[a*A-c*C]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2-c^2] && ZeroQ[a*A-b*B]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_]+C_.*Sin[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/
    (e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  Dist[(a*A-b*B-c*C)/(a^2-b^2-c^2),Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2-c^2] && NonzeroQ[a*A-b*B-c*C]


(* ::Code:: *)
Int[(A_.+C_.*Sin[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^2,x_Symbol] :=
  -(b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  Dist[(a*A-c*C)/(a^2-b^2-c^2),Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2-c^2] && NonzeroQ[a*A-c*C]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_])/(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^2,x_Symbol] :=
  (c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])/(e*(a^2-b^2-c^2)*(a+b*Cos[d+e*x]+c*Sin[d+e*x])) +
  Dist[(a*A-b*B)/(a^2-b^2-c^2),Int[1/(a+b*Cos[d+e*x]+c*Sin[d+e*x]),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2-c^2] && NonzeroQ[a*A-b*B]


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_]+C_.*Sin[d_.+e_.*x_])*(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*B-b*C-(a*C-c*A)*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2-c^2)) +
  Dist[1/((n+1)*(a^2-b^2-c^2)),
    Int[((n+1)*(a*A-b*B-c*C)+(n+2)*(a*B-b*A)*Cos[d+e*x]+(n+2)*(a*C-c*A)*Sin[d+e*x])*
      (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x]] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2-c^2] && RationalQ[n] && n<-1 && n!=-2


(* ::Code:: *)
Int[(A_.+C_.*Sin[d_.+e_.*x_])*(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (b*C+(a*C-c*A)*Cos[d+e*x]+b*A*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2-c^2)) +
  Dist[1/((n+1)*(a^2-b^2-c^2)),
    Int[((n+1)*(a*A-c*C)-(n+2)*b*A*Cos[d+e*x]+(n+2)*(a*C-c*A)*Sin[d+e*x])*
      (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x]] /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2-c^2] && RationalQ[n] && n<-1 && n!=-2


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_])*(a_.+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(c*B+c*A*Cos[d+e*x]+(a*B-b*A)*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1)/
    (e*(n+1)*(a^2-b^2-c^2)) +
  Dist[1/((n+1)*(a^2-b^2-c^2)),
    Int[((n+1)*(a*A-b*B)+(n+2)*(a*B-b*A)*Cos[d+e*x]-(n+2)*c*A*Sin[d+e*x])*
      (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2-c^2] && RationalQ[n] && n<-1 && n!=-2


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_]+C_.*Sin[d_.+e_.*x_])*(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  Dist[B/b,Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n+1),x]] +
  Dist[(b*A-a*B)/b,Int[(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n,x]] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && ZeroQ[b*C-c*B] && NonzeroQ[b*A-a*B] && RationalQ[n] && (n==-1/2 || ZeroQ[a^2-b^2-c^2])


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_]+C_.*Sin[d_.+e_.*x_])*(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (B*c-b*C-a*C*Cos[d+e*x]+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  Dist[1/(a*(n+1)),
    Int[(a*(b*B+c*C)*n + a^2*A*(n+1) + 
        (a^2*B*n + c*(b*C-c*B)*n + a*b*A*(n+1))*Cos[d+e*x] + 
        (a^2*C*n - b*(b*C-c*B)*n + a*c*A*(n+1))*Sin[d+e*x])*
      (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1),x]] /;
FreeQ[{a,b,c,d,e,A,B,C},x] && NonzeroQ[a^2-b^2-c^2] && RationalQ[n] && n>0


(* ::Code:: *)
Int[(A_.+C_.*Sin[d_.+e_.*x_])*(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  -(b*C+a*C*Cos[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  Dist[1/(a*(n+1)),
    Int[(a*c*C*n+a^2*A*(n+1)+(c*b*C*n+a*b*A*(n+1))*Cos[d+e*x]+(a^2*C*n-b^2*C*n+a*c*A*(n+1))*Sin[d+e*x])*
      (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1),x]] /;
FreeQ[{a,b,c,d,e,A,C},x] && NonzeroQ[a^2-b^2-c^2] && RationalQ[n] && n>0


(* ::Code:: *)
Int[(A_.+B_.*Cos[d_.+e_.*x_])*(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
  (B*c+a*B*Sin[d+e*x])*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^n/(a*e*(n+1)) + 
  Dist[1/(a*(n+1)),
    Int[(a*b*B*n+a^2*A*(n+1)+(a^2*B*n-c^2*B*n+a*b*A*(n+1))*Cos[d+e*x]+(b*c*B*n+a*c*A*(n+1))*Sin[d+e*x])*
      (a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1),x]] /;
FreeQ[{a,b,c,d,e,A,B},x] && NonzeroQ[a^2-b^2-c^2] && RationalQ[n] && n>0


