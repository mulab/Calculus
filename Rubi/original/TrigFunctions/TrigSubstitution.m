(* ::Package:: *)

(* ::Code:: *)
Int[u_.*(c_.*F_[a_.+b_.*x_]^n_)^m_,x_Symbol] :=
(Print["Int(1th)@TrigSubstitution.m"];
  Dist[c^(m-1/2)*Sqrt[c*F[a+b*x]^n]/F[a+b*x]^(n/2),Int[u*F[a+b*x]^(m*n),x]]) /;
FreeQ[{a,b,c},x] && IntegerQ[n/2] && IntegerQ[m-1/2] && m>0 && 
  MemberQ[{Sin,Cos,Tan,Cot,Sinh,Cosh,Tanh,Coth},F]

(* ::Code:: *)
Int[u_.*(c_.*F_[a_.+b_.*x_]^n_)^m_,x_Symbol] :=
(Print["Int(2th)@TrigSubstitution.m"];
  Dist[c^(m+1/2)*F[a+b*x]^(n/2)/Sqrt[c*F[a+b*x]^n],Int[u*F[a+b*x]^(m*n),x]]) /;
FreeQ[{a,b,c},x] && IntegerQ[n/2] && IntegerQ[m-1/2] && m<0 && 
  MemberQ[{Sin,Cos,Tan,Cot,Sinh,Cosh,Tanh,Coth},F]

(* ::Code:: *)
Int[u_*Cos[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(3th)@TrigSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Sin[c*(a+b*x)],u,x],x],x],x,Sin[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Sin[c*(a+b*x)],u,x,True]

(* ::Code:: *)
Int[u_*Cot[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(4th)@TrigSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Sin[c*(a+b*x)],u,x]/x,x],x],x,Sin[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Sin[c*(a+b*x)],u,x,True]

(* ::Code:: *)
Int[u_*Sin[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(5th)@TrigSubstitution.m"];
  -Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cos[c*(a+b*x)],u,x],x],x],x,Cos[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Cos[c*(a+b*x)],u,x,True]

(* ::Code:: *)
Int[u_*Tan[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(6th)@TrigSubstitution.m"];
  -Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cos[c*(a+b*x)],u,x]/x,x],x],x,Cos[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Cos[c*(a+b*x)],u,x,True]

(* ::Code:: *)
Int[u_*Csc[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
(Print["Int(7th)@TrigSubstitution.m"];
  -Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cot[c*(a+b*x)],u,x],x],x],x,Cot[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Cot[c*(a+b*x)],u,x,True] && NonsumQ[u]

(* ::Code:: *)
Int[u_*Tan[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
(Print["Int(8th)@TrigSubstitution.m"];
  -Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cot[c*(a+b*x)],u,x]/(x^n*(1+x^2)),x],x],x,Cot[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && IntegerQ[n] && FunctionOfQ[Cot[c*(a+b*x)],u,x,True] && TryPureTanSubst[u*Tan[c*(a+b*x)]^n,x]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(9th)@TrigSubstitution.m"];
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[f[Cot[a+b*x]],x]","Subst[Int[f[x]/(1+x^2),x],x,Cot[a+b*x]]/b",Hold[
  Dist[-1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Cot[v],u,x]/(1+x^2),x],x],x,Cot[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Cot[v],u,x,True] && TryPureTanSubst[u,x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(10th)@TrigSubstitution.m"];
  Module[{v=FunctionOfTrig[u,x]},
  Dist[-1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Cot[v],u,x]/(1+x^2),x],x],x,Cot[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Cot[v],u,x,True] && TryPureTanSubst[u,x]])]

(* ::Code:: *)
Int[u_*Sec[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
(Print["Int(11th)@TrigSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Tan[c*(a+b*x)],u,x],x],x],x,Tan[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Tan[c*(a+b*x)],u,x,True] && NonsumQ[u]

(* ::Code:: *)
Int[u_*Cot[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
(Print["Int(12th)@TrigSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Tan[c*(a+b*x)],u,x]/(x^n*(1+x^2)),x],x],x,Tan[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && IntegerQ[n] && FunctionOfQ[Tan[c*(a+b*x)],u,x,True] && TryPureTanSubst[u*Cot[c*(a+b*x)]^n,x]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(13th)@TrigSubstitution.m"];
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[f[Tan[a+b*x]],x]","Subst[Int[f[x]/(1+x^2),x],x,Tan[a+b*x]]/b",Hold[
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Tan[v],u,x]/(1+x^2),x],x],x,Tan[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Tan[v],u,x,True] && TryPureTanSubst[u,x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(14th)@TrigSubstitution.m"];
  Module[{v=FunctionOfTrig[u,x]},
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Tan[v],u,x]/(1+x^2),x],x],x,Tan[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Tan[v],u,x,True] && TryPureTanSubst[u,x]])]

(* ::Code:: *)
(* Int[u_*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(15th)@TrigSubstitution.m"];
  Sqrt[a+b*Sin[c+d*x]]/(Cos[c/2+d*x/2]+a/b*Sin[c/2+d*x/2])*
    (Int[u*Cos[c/2+d*x/2]*(a+b*Sin[c+d*x])^(n-1/2),x] +
     a/b*Int[u*Sin[c/2+d*x/2]*(a+b*Sin[c+d*x])^(n-1/2),x])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && IntegerQ[n-1/2] *)

(* ::Code:: *)
(* Int[u_*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(16th)@TrigSubstitution.m"];
  Sqrt[a+b*Cos[c+d*x]]/Cos[c/2+d*x/2]*Int[u*Cos[c/2+d*x/2]*(a+b*Cos[c+d*x])^(n-1/2),x]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && IntegerQ[n-1/2] *)

(* ::Code:: *)
(* Int[u_*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(17th)@TrigSubstitution.m"];
  Sqrt[a+b*Cos[c+d*x]]/Sin[c/2+d*x/2]*Int[u*Sin[c/2+d*x/2]*(a+b*Cos[c+d*x])^(n-1/2),x]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b] && IntegerQ[n-1/2] *)

(* ::Code:: *)
(* Int[u_*(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(18th)@TrigSubstitution.m"];
  Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(c*Cos[(d+e*x)/2]+(a-b)*Sin[(d+e*x)/2])*
    Dist[c,Int[u*Cos[(d+e*x)/2]*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1/2),x]] + 
  Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(c*Cos[(d+e*x)/2]+(a-b)*Sin[(d+e*x)/2])*
    Dist[a-b,Int[u*Sin[(d+e*x)/2]*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1/2),x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2] && IntegerQ[n-1/2] *)

