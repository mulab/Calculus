(* ::Package:: *)

(* ::Title:: *)

(* ::Item:: *)

Int[f_'[x_],x_Symbol] :=
(Print["Int(1th)@CalculusFunctions.m"];
  f[x]) /;
FreeQ[f,x]

(* ::Item:: *)

Int[Derivative[n_][f_][x_],x_Symbol] :=
(Print["Int(2th)@CalculusFunctions.m"];
  Derivative[n-1][f][x]) /;
FreeQ[{f,n},x]

(* ::Item:: *)

Int[u_*g_'[x_],x_Symbol] :=
(Print["Int(3th)@CalculusFunctions.m"];
  Subst[Int[Regularize[SubstFor[g[x],u,x],x],x],x,g[x]]) /;
FreeQ[g,x] && FunctionOfQ[g[x],u,x]

(* ::Item:: *)

Int[u_*Derivative[n_][g_][x_],x_Symbol] :=
(Print["Int(4th)@CalculusFunctions.m"];
  Subst[Int[Regularize[SubstFor[Derivative[n-1][g][x],u,x],x],x],x,Derivative[n-1][g][x]]) /;
FreeQ[{g,n},x] && FunctionOfQ[Derivative[n-1][g][x],u,x]

(* ::Item:: *)

Int[f_'[x_]*g_[x_] + f_[x_]*g_'[x_],x_Symbol] :=
(Print["Int(5th)@CalculusFunctions.m"];
  f[x]*g[x]) /;
FreeQ[{f,g},x]

(* ::Item:: *)

Int[(f_'[x_]*g_[x_] - f_[x_]*g_'[x_])/g_[x_]^2,x_Symbol] :=
(Print["Int(6th)@CalculusFunctions.m"];
  f[x]/g[x]) /;
FreeQ[{f,g},x]

(* ::Item:: *)

Int[(f_'[x_]*g_[x_] - f_[x_]*g_'[x_])/(f_[x_]*g_[x_]),x_Symbol] :=
(Print["Int(7th)@CalculusFunctions.m"];
  Log[f[x]/g[x]]) /;
FreeQ[{f,g},x]

(* ::Item:: *)

Int[(f_'[x_]*g_[x_] - f_[x_]*g_'[x_])/(f_[x_]^2 + g_[x_]^2),x_Symbol] :=
(Print["Int(8th)@CalculusFunctions.m"];
  ArcTan[f[x]/g[x]]) /;
FreeQ[{f,g},x]

(* ::Item:: *)

Int[(f_'[x_]*g_[x_] - f_[x_]*g_'[x_])/(f_[x_]^2 - g_[x_]^2),x_Symbol] :=
(Print["Int(9th)@CalculusFunctions.m"];
  Log[(f[x]-g[x])/(f[x]+g[x])]/2) /;
FreeQ[{f,g},x]
