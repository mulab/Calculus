(* ::Package:: *)

(* ::Code:: *)
Int[u_*Cosh[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(1th)@HyperbolicSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Sinh[c*(a+b*x)],u,x],x],x],x,Sinh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Sinh[c*(a+b*x)],u,x,True]

(* ::Code:: *)
Int[u_*Coth[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(2th)@HyperbolicSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Sinh[c*(a+b*x)],u,x]/x,x],x],x,Sinh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Sinh[c*(a+b*x)],u,x,True]

(* ::Code:: *)
Int[u_*Sinh[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(3th)@HyperbolicSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cosh[c*(a+b*x)],u,x],x],x],x,Cosh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Cosh[c*(a+b*x)],u,x,True]

(* ::Code:: *)
Int[u_*Tanh[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(4th)@HyperbolicSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cosh[c*(a+b*x)],u,x]/x,x],x],x,Cosh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Cosh[c*(a+b*x)],u,x,True]

(* ::Code:: *)
Int[u_*Csch[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
(Print["Int(5th)@HyperbolicSubstitution.m"];
  -Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Coth[c*(a+b*x)],u,x],x],x],x,Coth[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Coth[c*(a+b*x)],u,x,True] && NonsumQ[u]

(* ::Code:: *)
Int[u_*Tanh[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
(Print["Int(6th)@HyperbolicSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Coth[c*(a+b*x)],u,x]/(x^n*(1-x^2)),x],x],x,Coth[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && IntegerQ[n] && FunctionOfQ[Coth[c*(a+b*x)],u,x,True] && TryPureTanhSubst[u*Tanh[c*(a+b*x)]^n,x]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(7th)@HyperbolicSubstitution.m"];
  Module[{v=FunctionOfHyperbolic[u,x]},
  ShowStep["","Int[f[Coth[a+b*x]],x]","Subst[Int[f[x]/(1-x^2),x],x,Coth[a+b*x]]/b",Hold[
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Coth[v],u,x]/(1-x^2),x],x],x,Coth[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Coth[v],u,x,True] && TryPureTanhSubst[u,x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(8th)@HyperbolicSubstitution.m"];
  Module[{v=FunctionOfHyperbolic[u,x]},
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Coth[v],u,x]/(1-x^2),x],x],x,Coth[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Coth[v],u,x,True] && TryPureTanhSubst[u,x]])]

(* ::Code:: *)
Int[u_*Sech[c_.*(a_.+b_.*x_)]^2,x_Symbol] :=
(Print["Int(9th)@HyperbolicSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Tanh[c*(a+b*x)],u,x],x],x],x,Tanh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Tanh[c*(a+b*x)],u,x,True] && NonsumQ[u]

(* ::Code:: *)
Int[u_*Coth[c_.*(a_.+b_.*x_)]^n_.,x_Symbol] :=
(Print["Int(10th)@HyperbolicSubstitution.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Tanh[c*(a+b*x)],u,x]/(x^n*(1-x^2)),x],x],x,Tanh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && IntegerQ[n] && FunctionOfQ[Tanh[c*(a+b*x)],u,x,True] && TryPureTanhSubst[u*Coth[c*(a+b*x)]^n,x]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(11th)@HyperbolicSubstitution.m"];
  Module[{v=FunctionOfHyperbolic[u,x]},
  ShowStep["","Int[f[Tanh[a+b*x]],x]","Subst[Int[f[x]/(1-x^2),x],x,Tanh[a+b*x]]/b",Hold[
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Tanh[v],u,x]/(1-x^2),x],x],x,Tanh[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Tanh[v],u,x,True] && TryPureTanhSubst[u,x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(12th)@HyperbolicSubstitution.m"];
  Module[{v=FunctionOfHyperbolic[u,x]},
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Tanh[v],u,x]/(1-x^2),x],x],x,Tanh[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Tanh[v],u,x,True] && TryPureTanhSubst[u,x]])]

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(13th)@HyperbolicSubstitution.m"];
  Module[{v=TrigSimplify[u]},
  Int[v,x] /;
 v=!=u]) /;
Not[MatchQ[u,w_.*(a_.+b_.*v_)^m_.*(c_.+d_.*v_)^n_. /; 
		FreeQ[{a,b,c,d},x] && IntegersQ[m,n] && m<0 && n<0]]

