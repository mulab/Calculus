(* ::Package:: *)

(* ::Code:: *)
Int[u_.*(a_.*v_^m_)^p_, x_Symbol] :=
(Print["Int(1th)@GeneralIntegrationRules.m"];
  Module[{q=FractionalPart[p]},
  a^(p-q)*(a*v^m)^q/v^(m*q)*Int[u*v^(m*p),x]]) /;
FreeQ[{a,m,p},x] && IntegerQ[m*p] && 
  Not[MatchQ[u*(a*v^m)^p,(Sec[c_.+d_.*x]^2)^p /; FreeQ[{c,d},x] && p>0]] && 
  Not[MatchQ[u*(a*v^m)^p,(Csc[c_.+d_.*x]^2)^p /; FreeQ[{c,d},x] && p>0]] && 
  Not[MatchQ[u*(a*v^m)^p,(Sech[c_.+d_.*x]^2)^p /; FreeQ[{c,d},x] && p>0]] && 
  Not[MatchQ[u*(a*v^m)^p,(-Csch[c_.+d_.*x]^2)^p /; FreeQ[{c,d},x] && p>0]]

(* ::Code:: *)
Int[u_.*(a_.*v_^m_.*w_^n_.)^p_, x_Symbol] :=
(Print["Int(2th)@GeneralIntegrationRules.m"];
  Module[{q=FractionalPart[p]},
  a^(p-q)*(a*v^m*w^n)^q/(v^(m*q)*w^(n*q))*Int[u*v^(m*p)*w^(n*p),x]]) /;
FreeQ[{a,m,n,p},x] && IntegerQ[m*p] && IntegerQ[n*p]

(* ::Code:: *)
Int[u_*x_^m_.,x_Symbol] :=
(Print["Int(3th)@GeneralIntegrationRules.m"];
  Dist[1/(m+1),Subst[Int[Regularize[SubstFor[x^(m+1),u,x],x],x],x,x^(m+1)]]) /;
FreeQ[m,x] && NonzeroQ[m+1] && FunctionOfQ[x^(m+1),u,x]

(* ::Code:: *)
Int[u_*Log[v_],x_Symbol] :=
(Print["Int(4th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[v,u*(1-v),x]},
  w*PolyLog[2,1-v] /;
 Not[FalseQ[w]]])

(* ::Code:: *)
Int[u_*PolyLog[n_,v_],x_Symbol] :=
(Print["Int(5th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[v,u*v,x]},
  w*PolyLog[n+1,v] /;
 Not[FalseQ[w]]]) /;
FreeQ[n,x]

(* ::Code:: *)
If[ShowSteps,

Int[u_*f_[a1___,g_[b1___,h_[c1___,v_,c2___],b2___],a2___],x_Symbol] :=
(Print["Int(6th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[v,u,x]},
  ShowStep["","Int[f[g[x]]*g'[x],x]","Subst[Int[f[x],x],x,g[x]]",Hold[
  Dist[z,Subst[Int[f[a1,g[b1,h[c1,x,c2],b2],a2],x],x,v]]]] /;
 Not[FalseQ[z]]]) /;
SimplifyFlag && FreeQ[{a1,a2,b1,b2,c1,c2,f,g},x],

Int[u_*f_[a1___,g_[b1___,h_[c1___,v_,c2___],b2___],a2___],x_Symbol] :=
(Print["Int(7th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[v,u,x]},
  Dist[z,Subst[Int[f[a1,g[b1,h[c1,x,c2],b2],a2],x],x,v]] /;
 Not[FalseQ[z]]]) /;
SimplifyFlag && FreeQ[{a1,a2,b1,b2,c1,c2,f,g},x]]

(* ::Code:: *)
If[ShowSteps,

Int[u_*f_[a1___,g_[b1___,v_,b2___],a2___],x_Symbol] :=
(Print["Int(8th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[v,u,x]},
  ShowStep["","Int[f[g[x]]*g'[x],x]","Subst[Int[f[x],x],x,g[x]]",Hold[
  Dist[z,Subst[Int[f[a1,g[b1,x,b2],a2],x],x,v]]]] /;
 Not[FalseQ[z]]]) /;
SimplifyFlag && FreeQ[{a1,a2,b1,b2,f,g},x],

Int[u_*f_[a1___,g_[b1___,v_,b2___],a2___],x_Symbol] :=
(Print["Int(9th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[v,u,x]},
  Dist[z,Subst[Int[f[a1,g[b1,x,b2],a2],x],x,v]] /;
 Not[FalseQ[z]]]) /;
SimplifyFlag && FreeQ[{a1,a2,b1,b2,f,g},x]]

(* ::Code:: *)
If[ShowSteps,

Int[u_*f_[a1___,v_,a2___],x_Symbol] :=
(Print["Int(10th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[v,u,x]},
  ShowStep["","Int[f[g[x]]*g'[x],x]","Subst[Int[f[x],x],x,g[x]]",Hold[
  Dist[z,Subst[Int[f[a1,x,a2],x],x,v]]]] /;
 Not[FalseQ[z]]]) /;
SimplifyFlag && FreeQ[{a1,a2,f},x],

Int[u_*f_[a1___,v_,a2___],x_Symbol] :=
(Print["Int(11th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[v,u,x]},
  Dist[z,Subst[Int[f[a1,x,a2],x],x,v]] /;
 Not[FalseQ[z]]]) /;
SimplifyFlag && FreeQ[{a1,a2,f},x]]

(* ::Code:: *)
If[ShowSteps,

Int[u_*v_,x_Symbol] :=
(Print["Int(12th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[v,u,x]},
  ShowStep["","Int[g[x]*g'[x],x]","Subst[Int[x,x],x,g[x]]",Hold[
  Dist[z,Subst[Int[x,x],x,v]]]] /;
 Not[FalseQ[z]]]) /;
SimplifyFlag,

Int[u_*v_,x_Symbol] :=
(Print["Int(13th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[v,u,x]},
  Dist[z,Subst[Int[x,x],x,v]] /;
 Not[FalseQ[z]]])]

(* ::Code:: *)
If[ShowSteps,

Int[u1_^n_*u2_^n_*v_,x_Symbol] :=
(Print["Int(14th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[u1*u2,v,x]},
  ShowStep["If nonzero[n+1],","Int[f[x]^n*g[x]^n*D[f[x]*g[x],x],x]",
							  "f[x]^(n+1)*g[x]^(n+1)/(n+1)",Hold[
  w*u1^(n+1)*u2^(n+1)/(n+1)]] /;
 Not[FalseQ[w]]]) /;
SimplifyFlag && FreeQ[n,x] && NonzeroQ[n+1] && (SumQ[v] || NonsumQ[u1*u2] || NonzeroQ[n-1]),

Int[u1_^n_*u2_^n_*v_,x_Symbol] :=
(Print["Int(15th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[u1*u2,v,x]},
  w*u1^(n+1)*u2^(n+1)/(n+1) /;
 Not[FalseQ[w]]]) /;
FreeQ[n,x] && NonzeroQ[n+1] && (SumQ[v] || NonsumQ[u1*u2] || NonzeroQ[n-1])]

(* ::Code:: *)
If[ShowSteps,

Int[x_^m_.*u_^n_.*v_,x_Symbol] :=
(Print["Int(16th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[x*u,x^(m-n)*v,x]},
  ShowStep["If nonzero[n+1],","Int[f[x]^n*g[x]^n*D[f[x]*g[x],x],x]",
							  "f[x]^(n+1)*g[x]^(n+1)/(n+1)",Hold[
  w*x^(n+1)*u^(n+1)/(n+1)]] /;
 Not[FalseQ[w]]]) /;
SimplifyFlag && FreeQ[n,x] && NonzeroQ[n+1] && (SumQ[v] || NonsumQ[u] || NonzeroQ[n-1]),

Int[x_^m_.*u_^n_.*v_,x_Symbol] :=
(Print["Int(17th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[x*u,x^(m-n)*v,x]},
  w*x^(n+1)*u^(n+1)/(n+1) /;
 Not[FalseQ[w]]]) /;
FreeQ[n,x] && NonzeroQ[n+1] && (SumQ[v] || NonsumQ[u] || NonzeroQ[n-1])]

(* ::Code:: *)
If[ShowSteps,

Int[x_^m_.*u_^n_.*v_,x_Symbol] :=
(Print["Int(18th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[u,v,x]},
  ShowStep["If nonzero[n+1],","Int[x^m*f[x]^n*f'[x],x]",
				"x^m*f[x]^(n+1)/(n+1) - m/(n+1)*Int[x^(m-1)*f[x]^(n+1),x]",Hold[
  w*x^m*u^(n+1)/(n+1) -
    Dist[m/(n+1)*w,Int[x^(m-1)*u^(n+1),x]]]] /;
 Not[FalseQ[w]]]) /;
SimplifyFlag && FreeQ[n,x] && NonzeroQ[n+1] && IntegerQ[m] && m>0 &&
	(SumQ[v] || NonsumQ[u] || NonzeroQ[n-1]),

Int[x_^m_.*u_^n_.*v_,x_Symbol] :=
(Print["Int(19th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[u,v,x]},
  w*x^m*u^(n+1)/(n+1) -
    Dist[m/(n+1)*w,Int[x^(m-1)*u^(n+1),x]] /;
 Not[FalseQ[w]]]) /;
FreeQ[n,x] && NonzeroQ[n+1] && IntegerQ[m] && m>0 && (SumQ[v] || NonsumQ[u] || NonzeroQ[n-1])]

(* ::Code:: *)
Int[u_*v_,x_Symbol] :=
(Print["Int(20th)@GeneralIntegrationRules.m"];
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},
  Subst[Int[Regularize[SubstFor[w,u,x],x],x],x,w] /;
 FunctionOfQ[w,u,x]]) /;
SumQ[v] && PolynomialQ[v,x]

(* ::Code:: *)
Int[u_*(a_.+b_.*x_)^m_.,x_Symbol] :=
(Print["Int(21th)@GeneralIntegrationRules.m"];
  Dist[1/(b*(m+1)),Subst[Int[Regularize[SubstFor[(a+b*x)^(m+1),u,x],x],x],x,(a+b*x)^(m+1)]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1] && FunctionOfQ[(a+b*x)^(m+1),u,x] 

(* ::Code:: *)
If[ShowSteps,

Int[u_/x_,x_Symbol] :=
(Print["Int(22th)@GeneralIntegrationRules.m"];
  Module[{lst=PowerVariableExpn[u,0,x]},
  ShowStep["","Int[f[(c*x)^n]/x,x]","Subst[Int[f[x]/x,x],x,(c*x)^n]/n",Hold[
  Dist[1/lst[[2]],Subst[Int[Regularize[lst[[1]]/x,x],x],x,(lst[[3]]*x)^lst[[2]]]]]] /;
 Not[FalseQ[lst]] && NonzeroQ[lst[[2]]]]) /;
SimplifyFlag && NonsumQ[u] && Not[RationalFunctionQ[u,x]],

Int[u_/x_,x_Symbol] :=
(Print["Int(23th)@GeneralIntegrationRules.m"];
  Module[{lst=PowerVariableExpn[u,0,x]},
  Dist[1/lst[[2]],Subst[Int[Regularize[lst[[1]]/x,x],x],x,(lst[[3]]*x)^lst[[2]]]] /;
 Not[FalseQ[lst]] && NonzeroQ[lst[[2]]]]) /;
NonsumQ[u] && Not[RationalFunctionQ[u,x]]]

(* ::Code:: *)
If[ShowSteps,

Int[u_*x_^m_.,x_Symbol] :=
(Print["Int(24th)@GeneralIntegrationRules.m"];
  Module[{lst=PowerVariableExpn[u,m+1,x]},
  ShowStep["If g=GCD[m+1,n]>1,","Int[x^m*f[x^n],x]",
		"Subst[Int[x^((m+1)/g-1)*f[x^(n/g)],x],x,x^g]/g",Hold[
  Dist[1/lst[[2]],Subst[Int[Regularize[lst[[1]]/x,x],x],x,(lst[[3]]*x)^lst[[2]]]]]] /;
 NotFalseQ[lst] && NonzeroQ[lst[[2]]-m-1]]) /;
SimplifyFlag && IntegerQ[m] && m!=-1 && NonsumQ[u] && (m>0 || Not[AlgebraicFunctionQ[u,x]]),

Int[u_*x_^m_.,x_Symbol] :=
(Print["Int(25th)@GeneralIntegrationRules.m"];
  Module[{lst=PowerVariableExpn[u,m+1,x]},
  Dist[1/lst[[2]],Subst[Int[Regularize[lst[[1]]/x,x],x],x,(lst[[3]]*x)^lst[[2]]]] /;
 NotFalseQ[lst] && NonzeroQ[lst[[2]]-m-1]]) /;
IntegerQ[m] && m!=-1 && NonsumQ[u] && (m>0 || Not[AlgebraicFunctionQ[u,x]])]

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(26th)@GeneralIntegrationRules.m"];
  Int[NormalForm[Expand[TrigReduce[u],x],x],x]) /;
ProductQ[u] && Catch[Scan[Function[If[Not[LinearSinCosQ[#,x]],Throw[False]]],u];True]

(* ::Code:: *)
LinearSinCosQ[u_^n_.,x_Symbol] :=
  IntegerQ[n] && n>0 && (SinQ[u] || CosQ[u]) && LinearQ[u[[1]],x]

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(27th)@GeneralIntegrationRules.m"];
  Int[NormalForm[Expand[TrigReduce[u],x],x],x]) /;
ProductQ[u] && Catch[Scan[Function[If[Not[LinearSinhCoshQ[#,x]],Throw[False]]],u];True]

(* ::Code:: *)
LinearSinhCoshQ[u_^n_.,x_Symbol] :=
  IntegerQ[n] && n>0 && (SinhQ[u] || CoshQ[u]) && LinearQ[u[[1]],x]

(* ::Code:: *)
Int[u_*Sin[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(28th)@GeneralIntegrationRules.m"];
  -Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cos[c*(a+b*x)],u,x],x],x],x,Cos[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Cos[c*(a+b*x)],u,x]

(* ::Code:: *)
Int[u_*Cos[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(29th)@GeneralIntegrationRules.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Sin[c*(a+b*x)],u,x],x],x],x,Sin[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Sin[c*(a+b*x)],u,x]

(* ::Code:: *)
Int[u_*Tan[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(30th)@GeneralIntegrationRules.m"];
  -Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cos[c*(a+b*x)],u,x]/x,x],x],x,Cos[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Cos[c*(a+b*x)],u,x]

(* ::Code:: *)
Int[u_*Cot[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(31th)@GeneralIntegrationRules.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Sin[c*(a+b*x)],u,x]/x,x],x],x,Sin[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Sin[c*(a+b*x)],u,x]

(* ::Code:: *)
Int[u_*Sec[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
(Print["Int(32th)@GeneralIntegrationRules.m"];
  Dist[1/(b*c),
    Subst[Int[Regularize[(1+x^2)^((n-2)/2)*SubstFor[Tan[c*(a+b*x)],u,x],x],x],x,Tan[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && EvenQ[n] && FunctionOfQ[Tan[c*(a+b*x)],u,x] && NonsumQ[u]

(* ::Code:: *)
Int[u_*Csc[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
(Print["Int(33th)@GeneralIntegrationRules.m"];
  -Dist[1/(b*c),
    Subst[Int[Regularize[(1+x^2)^((n-2)/2)*SubstFor[Cot[c*(a+b*x)],u,x],x],x],x,Cot[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && EvenQ[n] && FunctionOfQ[Cot[c*(a+b*x)],u,x] && NonsumQ[u]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(34th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[f[Sin[a+b*x]]*Cos[a+b*x],x]","Subst[Int[f[x],x],x,Sin[a+b*x]]/b",Hold[
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Sin[v],u/Cos[v],x],x],x],x,Sin[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Sin[v],u/Cos[v],x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(35th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfTrig[u,x]},
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Sin[v],u/Cos[v],x],x],x],x,Sin[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Sin[v],u/Cos[v],x]])]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(36th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[f[Cos[a+b*x]]*Sin[a+b*x],x]","-Subst[Int[f[x],x],x,Cos[a+b*x]]/b",Hold[
  -Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Cos[v],u/Sin[v],x],x],x],x,Cos[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Cos[v],u/Sin[v],x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(37th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfTrig[u,x]},
  -Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Cos[v],u/Sin[v],x],x],x],x,Cos[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Cos[v],u/Sin[v],x]])]

(* ::Code:: *)
Int[u_*Sec[a_.+b_.*x_]*Csc[a_.+b_.*x_],x_Symbol] :=
(Print["Int(38th)@GeneralIntegrationRules.m"];
  Dist[1/b,Subst[Int[Regularize[SubstFor[Log[Tan[a+b*x]],u,x],x],x],x,Log[Tan[a+b*x]]]]) /;
FreeQ[{a,b},x] && FunctionOfQ[Log[Tan[a+b*x]],u,x]

(* ::Code:: *)
Int[u_*Sec[a_.+b_.*x_]*Csc[a_.+b_.*x_],x_Symbol] :=
(Print["Int(39th)@GeneralIntegrationRules.m"];
  -Dist[1/b,Subst[Int[Regularize[SubstFor[Log[Cot[a+b*x]],u,x],x],x],x,Log[Cot[a+b*x]]]]) /;
FreeQ[{a,b},x] && FunctionOfQ[Log[Cot[a+b*x]],u,x]

(* ::Code:: *)
Int[u_*Cos[a_.+b_.*x_],x_Symbol] :=
(Print["Int(40th)@GeneralIntegrationRules.m"];
  Dist[2/b,Subst[Int[Regularize[SubstFor[Cos[a/2+b/2*x]*Sin[a/2+b/2*x],u,x],x],x],x,
				Cos[a/2+b/2*x]*Sin[a/2+b/2*x]]]) /;
NonsumQ[u] && FreeQ[{a,b},x] && FunctionOfQ[Cos[a/2+b/2*x]*Sin[a/2+b/2*x],u,x]

(* ::Code:: *)
Int[u_*Sinh[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(41th)@GeneralIntegrationRules.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cosh[c*(a+b*x)],u,x],x],x],x,Cosh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Cosh[c*(a+b*x)],u,x]

(* ::Code:: *)
Int[u_*Cosh[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(42th)@GeneralIntegrationRules.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Sinh[c*(a+b*x)],u,x],x],x],x,Sinh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Sinh[c*(a+b*x)],u,x]

(* ::Code:: *)
Int[u_*Tanh[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(43th)@GeneralIntegrationRules.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Cosh[c*(a+b*x)],u,x]/x,x],x],x,Cosh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Cosh[c*(a+b*x)],u,x]

(* ::Code:: *)
Int[u_*Coth[c_.*(a_.+b_.*x_)],x_Symbol] :=
(Print["Int(44th)@GeneralIntegrationRules.m"];
  Dist[1/(b*c),Subst[Int[Regularize[SubstFor[Sinh[c*(a+b*x)],u,x]/x,x],x],x,Sinh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && FunctionOfQ[Sinh[c*(a+b*x)],u,x]

(* ::Code:: *)
Int[u_*Sech[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
(Print["Int(45th)@GeneralIntegrationRules.m"];
  Dist[1/(b*c),
    Subst[Int[Regularize[(1-x^2)^((n-2)/2)*SubstFor[Tanh[c*(a+b*x)],u,x],x],x],x,Tanh[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && EvenQ[n] && FunctionOfQ[Tanh[c*(a+b*x)],u,x] && NonsumQ[u]

(* ::Code:: *)
Int[u_*Csch[c_.*(a_.+b_.*x_)]^n_,x_Symbol] :=
(Print["Int(46th)@GeneralIntegrationRules.m"];
  -Dist[1/(b*c),
    Subst[Int[Regularize[(-1+x^2)^((n-2)/2)*SubstFor[Coth[c*(a+b*x)],u,x],x],x],x,Coth[c*(a+b*x)]]]) /;
FreeQ[{a,b,c},x] && EvenQ[n] && FunctionOfQ[Coth[c*(a+b*x)],u,x] && NonsumQ[u]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(47th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfHyperbolic[u,x]},
  ShowStep["","Int[f[Sinh[a+b*x]]*Cosh[a+b*x],x]","Subst[Int[f[x],x],x,Sinh[a+b*x]]/b",Hold[
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Sinh[v],u/Cosh[v],x],x],x],x,Sinh[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Sinh[v],u/Cosh[v],x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(48th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfHyperbolic[u,x]},
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Sinh[v],u/Cosh[v],x],x],x],x,Sinh[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Sinh[v],u/Cosh[v],x]])]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(49th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfHyperbolic[u,x]},
  ShowStep["","Int[f[Cosh[a+b*x]]*Sinh[a+b*x],x]","Subst[Int[f[x],x],x,Cosh[a+b*x]]/b",Hold[
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Cosh[v],u/Sinh[v],x],x],x],x,Cosh[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Cosh[v],u/Sinh[v],x] ]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(50th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfHyperbolic[u,x]},
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Cosh[v],u/Sinh[v],x],x],x],x,Cosh[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Cosh[v],u/Sinh[v],x] ])]

(* ::Code:: *)
Int[u_*Sech[a_.+b_.*x_]*Csch[a_.+b_.*x_],x_Symbol] :=
(Print["Int(51th)@GeneralIntegrationRules.m"];
  Dist[1/b,Subst[Int[Regularize[SubstFor[Log[Tanh[a+b*x]],u,x],x],x],x,Log[Tanh[a+b*x]]]]) /;
FreeQ[{a,b},x] && FunctionOfQ[Log[Tanh[a+b*x]],u,x]

(* ::Code:: *)
Int[u_*Sech[a_.+b_.*x_]*Csch[a_.+b_.*x_],x_Symbol] :=
(Print["Int(52th)@GeneralIntegrationRules.m"];
  -Dist[1/b,Subst[Int[Regularize[SubstFor[Log[Coth[a+b*x]],u,x],x],x],x,Log[Coth[a+b*x]]]]) /;
FreeQ[{a,b},x] && FunctionOfQ[Log[Coth[a+b*x]],u,x]

(* ::Code:: *)
Int[u_*Cosh[a_.+b_.*x_],x_Symbol] :=
(Print["Int(53th)@GeneralIntegrationRules.m"];
  Dist[2/b,Subst[Int[Regularize[SubstFor[Cosh[a/2+b/2*x]*Sinh[a/2+b/2*x],u,x],x],x],x,
				Cosh[a/2+b/2*x]*Sinh[a/2+b/2*x]]]) /;
NonsumQ[u] && FreeQ[{a,b},x] && FunctionOfQ[Cosh[a/2+b/2*x]*Sinh[a/2+b/2*x],u,x]

(* ::Code:: *)
If[ShowSteps,

Int[x_^m_.*u_^(-1+a_.*x_^m_.)*v_,x_Symbol] :=
(Print["Int(54th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[u,v,x]},
  ShowStep["If m>0,","Int[x^m*f[x]^(-1+a*x^m)*f'[x],x]",
				"f[x]^(a*x^m)/a - m*Int[x^(m-1)*f[x]^(a*x^m)*Log[f[x]],x]",Hold[
  w*u^(a*x^m)/a -
    Dist[m*w,Int[x^(m-1)*u^(a*x^m)*Log[u],x]]]] /;
 Not[FalseQ[w]]]) /;
SimplifyFlag && FreeQ[a,x] && RationalQ[m] && m>0,

Int[x_^m_.*u_^(-1+a_.*x_^m_.)*v_,x_Symbol] :=
(Print["Int(55th)@GeneralIntegrationRules.m"];
  Module[{w=DerivativeDivides[u,v,x]},
  w*u^(a*x^m)/a -
    Dist[m*w,Int[x^(m-1)*u^(a*x^m)*Log[u],x]] /;
 Not[FalseQ[w]]]) /;
FreeQ[a,x] && RationalQ[m] && m>0]

(* ::Code:: *)
(* If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(56th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[f[Cot[a+b*x]],x]","-Subst[Int[f[x]/(1+x^2),x],x,Cot[a+b*x]]/b",Hold[
  -Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Cot[v],u,x]/(1+x^2),x],x],x,Cot[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Cot[v],u,x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(57th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfTrig[u,x]},
  -Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Cot[v],u,x]/(1+x^2),x],x],x,Cot[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Cot[v],u,x]])] *)

(* ::Code:: *)
(* If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(58th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfTrig[u,x]},
  ShowStep["","Int[f[Tan[a+b*x]],x]","Subst[Int[f[x]/(1+x^2),x],x,Tan[a+b*x]]/b",Hold[
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Tan[v],u,x]/(1+x^2),x],x],x,Tan[v]]]]] /;
 NotFalseQ[v] && FunctionOfQ[Tan[v],u,x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(59th)@GeneralIntegrationRules.m"];
  Module[{v=FunctionOfTrig[u,x]},
  Dist[1/Coefficient[v,x,1],Subst[Int[Regularize[SubstFor[Tan[v],u,x]/(1+x^2),x],x],x,Tan[v]]] /;
 NotFalseQ[v] && FunctionOfQ[Tan[v],u,x]])] *)

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(60th)@GeneralIntegrationRules.m"];
  Subst[Int[Regularize[SubstFor[Tan[x],u,x]/(1+x^2),x],x],x,Tan[x]]) /;
FunctionOfQ[Tan[x],u,x] && FunctionOfTanWeight[u,x,x]>=0 && TryTanSubst[u,x]

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(61th)@GeneralIntegrationRules.m"];
  -Subst[Int[Regularize[SubstFor[Cot[x],u,x]/(1+x^2),x],x],x,Cot[x]]) /;
FunctionOfQ[Cot[x],u,x] && FunctionOfTanWeight[u,x,x]<0 && TryTanSubst[u,x]

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(62th)@GeneralIntegrationRules.m"];
  Subst[Int[Regularize[SubstFor[Tanh[x],u,x]/(1-x^2),x],x],x,Tanh[x]]) /;
FunctionOfQ[Tanh[x],u,x] && FunctionOfTanhWeight[u,x,x]>=0 && TryTanhSubst[u,x]

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(63th)@GeneralIntegrationRules.m"];
  Subst[Int[Regularize[SubstFor[Coth[x],u,x]/(1-x^2),x],x],x,Coth[x]]) /;
FunctionOfQ[Coth[x],u,x] && FunctionOfTanhWeight[u,x,x]<0 && TryTanhSubst[u,x]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(64th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfExponentialOfLinear[u,x]},
  If[lst[[4]]===E,
    ShowStep["","Int[f[E^(a+b*x)],x]","Subst[Int[f[x]/x,x],x,E^(a+b*x)]/b",Hold[
    Dist[1/lst[[3]],Subst[Int[Regularize[lst[[1]]/x,x],x],x,E^(lst[[2]]+lst[[3]]*x)]]]],
  ShowStep["","Int[g[f^(a+b*x)],x]","Subst[Int[g[x]/x,x],x,f^(a+b*x)]/(b*Log[f])",Hold[
  Dist[1/(lst[[3]]*Log[lst[[4]]]),
       Subst[Int[Regularize[lst[[1]]/x,x],x],x,lst[[4]]^(lst[[2]]+lst[[3]]*x)]]]]] /;
 Not[FalseQ[lst]]]) /;
SimplifyFlag && 
Not[MatchQ[u,v_^n_. /; SumQ[v] && IntegerQ[n] && n>0]] &&
Not[MatchQ[u,v_^n_.*f_^(a_.+b_.*x) /; FreeQ[{a,b,f},x] && SumQ[v] && IntegerQ[n] && n>0]] &&
Not[MatchQ[u,1/(a_.+b_.*f_^(d_.+e_.*x)+c_.*f_^(g_.+h_.*x)) /; 
	FreeQ[{a,b,c,d,e,f,g,h},x] && ZeroQ[g-2*d] && ZeroQ[h-2*e]]] &&
FalseQ[FunctionOfHyperbolic[u,x]] ,

Int[u_,x_Symbol] :=
(Print["Int(65th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfExponentialOfLinear[u,x]},
  Dist[1/(lst[[3]]*Log[lst[[4]]]),
	   Subst[Int[Regularize[lst[[1]]/x,x],x],x,lst[[4]]^(lst[[2]]+lst[[3]]*x)]] /;
 Not[FalseQ[lst]]]) /;
Not[MatchQ[u,v_^n_. /; SumQ[v] && IntegerQ[n] && n>0]] &&
Not[MatchQ[u,v_^n_.*f_^(a_.+b_.*x) /; FreeQ[{a,b,f},x] && SumQ[v] && IntegerQ[n] && n>0]] &&
Not[MatchQ[u,1/(a_.+b_.*f_^(d_.+e_.*x)+c_.*f_^(g_.+h_.*x)) /; 
	FreeQ[{a,b,c,d,e,f,g,h},x] && ZeroQ[g-2*d] && ZeroQ[h-2*e]]] &&
FalseQ[FunctionOfHyperbolic[u,x]]  ]

(* ::Code:: *)
Int[x_^m_.*f_^(a_.+b_.*x_^n_.),x_Symbol] :=
(Print["Int(66th)@GeneralIntegrationRules.m"];
  -Subst[Int[f^(a+b*x^(-n))/x^(m+2),x],x,1/x]) /;
FreeQ[{a,b,f},x] && IntegersQ[m,n] && n<0 && m<-1 && GCD[m+1,n]==1

(* ::Code:: *)
Int[x_^m_.*f_[a_.+b_.*x_^n_]^p_.,x_Symbol] :=
(Print["Int(67th)@GeneralIntegrationRules.m"];
  -Subst[Int[f[a+b*x^(-n)]^p/x^(m+2),x],x,1/x]) /;
FreeQ[{a,b,f,p},x] && IntegersQ[m,n] && n<0 && m<-1 && GCD[m+1,n]==1

(* ::Code:: *)
Int[u_*(a_+b_.*x_^n_)^m_,x_Symbol] :=
(Print["Int(68th)@GeneralIntegrationRules.m"];
  (a+b*x^n)^m/(x^(m*n)*(b+a/x^n)^m)*Int[u*x^(m*n)*(b+a/x^n)^m,x]) /;
FreeQ[{a,b},x] && FractionQ[m] && IntegerQ[n] && n<-1 && u===ExpnExpand[u,x]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(69th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForFractionalPowerOfLinear[u,x]},
  ShowStep["","Int[f[(a+b*x)^(1/n),x],x]",
			"n/b*Subst[Int[x^(n-1)*f[x,-a/b+x^n/b],x],x,(a+b*x)^(1/n)]",Hold[
  Dist[lst[[2]]*lst[[4]],Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])]]]] /;
 NotFalseQ[lst] && SubstForFractionalPowerQ[u,lst[[3]],x]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(70th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForFractionalPowerOfLinear[u,x]},
  Dist[lst[[2]]*lst[[4]],Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])]] /;
 NotFalseQ[lst] && SubstForFractionalPowerQ[u,lst[[3]],x]])]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(71th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForFractionalPowerOfQuotientOfLinears[u,x]},
  ShowStep["","Int[f[((a+b*x)/(c+d*x))^(1/n),x],x]",
"n*(b*c-a*d)*Subst[Int[x^(n-1)*f[x,(-a+c*x^n)/(b-d*x^n)]/(b-d*x^n)^2,x],x,((a+b*x)/(c+d*x))^(1/n)]",Hold[
  Dist[lst[[2]]*lst[[4]],Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])]]]] /;
 NotFalseQ[lst]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(72th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForFractionalPowerOfQuotientOfLinears[u,x]},
  Dist[lst[[2]]*lst[[4]],Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])]] /;
 NotFalseQ[lst]])]

(* ::Code:: *)
Int[u_*(a_+b_.*x_)^m_.,x_Symbol] :=
(Print["Int(73th)@GeneralIntegrationRules.m"];
  Dist[1/b,Subst[Int[x^m*Regularize[SubstFor[a+b*x,u,x],x],x],x,a+b*x]]) /;
FreeQ[{a,b,m},x] && FunctionOfQ[a+b*x,u,x]

(* ::Code:: *)
Int[x_^m_./(a_+b_.*(c_+d_.*x_)^n_), x_Symbol] :=
(Print["Int(74th)@GeneralIntegrationRules.m"];
  Dist[1/d,Subst[Int[(-c/d+x/d)^m/(a+b*x^n),x],x,c+d*x]]) /;
FreeQ[{a,b,c,d},x] && IntegersQ[m,n] && n>2

(* ::Code:: *)
Int[(e_+f_.*x_)^m_.*(a_+b_.*(c_+d_.*x_)^n_)^p_, x_Symbol] :=
(Print["Int(75th)@GeneralIntegrationRules.m"];
  Dist[(f/d)^m/d,Subst[Int[x^m*(a+b*x^n)^p,x],x,c+d*x]]) /;
FreeQ[{a,b,c,d,e,f},x] && IntegersQ[m,n,p] && ZeroQ[d*e-c*f]

(* ::Code:: *)
Int[(a_.+b_.*x_)^m_.*f_[c_.+d_.*x_]^p_.,x_Symbol] :=
(Print["Int(76th)@GeneralIntegrationRules.m"];
  Dist[1/b,Subst[Int[x^m*f[c-a*d/b+d*x/b]^p,x],x,a+b*x]]) /;
FreeQ[{a,b,c,d,m},x] && RationalQ[p] && Not[a===0 && b===1] &&
	MemberQ[{Sin,Cos,Sec,Csc,Sinh,Cosh,Sech,Csch},f]

(* ::Code:: *)
Int[(a_.+b_.*x_)^m_*(c_.+d_.*x_+e_.*x_^2)^n_,x_Symbol] :=
(Print["Int(77th)@GeneralIntegrationRules.m"];
  Dist[1/b,Subst[Int[x^m*(c-a*d/b+a^2*e/b^2+(d/b-2*a*e/b^2)*x+e*x^2/b^2)^n,x],x,a+b*x]]) /;
FreeQ[{a,b,c,d,e,m,n},x] && FractionQ[n] && Not[a===0 && b===1]

(* ::Code:: *)
Int[(u_+x_^p_.)^n_*v_,x_Symbol] :=
(Print["Int(78th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[u,v,x]},
  z*(u+x^p)^(n+1)/(n+1) -
  Dist[z*p,Int[x^(p-1)*(u+x^p)^n,x]] /;
 Not[FalseQ[z]]]) /;
IntegerQ[p] && RationalQ[n] && NonzeroQ[n+1] && Not[AlgebraicFunctionQ[v,x]]

(* ::Code:: *)
Int[x_^m_.*(u_+x_^p_.)^n_*v_,x_Symbol] :=
(Print["Int(79th)@GeneralIntegrationRules.m"];
  Module[{z=DerivativeDivides[u,v,x]},
  z*x^m*(u+x^p)^(n+1)/(n+1) -
  Dist[z*p,Int[x^(m+p-1)*(u+x^p)^n,x]] -
  Dist[z*m/(n+1),Int[x^(m-1)*(u+x^p)^(n+1),x]] /;
 Not[FalseQ[z]]]) /;
IntegersQ[m,p] && RationalQ[n] && NonzeroQ[n+1]

(* ::Code:: *)
Int[Log[u_],x_Symbol] :=
(Print["Int(80th)@GeneralIntegrationRules.m"];
  x*Log[u] -
  Int[Regularize[x*D[u,x]/u,x],x]) /;
InverseFunctionFreeQ[u,x]

(* ::Code:: *)
Int[Log[u_]/x_,x_Symbol] :=
(Print["Int(81th)@GeneralIntegrationRules.m"];
  Module[{v=D[u,x]/u},
  Log[u]*Log[x] -
  Int[Regularize[Log[x]*v,x],x] /;
 RationalFunctionQ[v,x]]) /;
Not[BinomialTest[u,x] && BinomialTest[u,x][[3]]^2===1]

(* ::Code:: *)
Int[Log[u_]/(a_+b_.*x_),x_Symbol] :=
(Print["Int(82th)@GeneralIntegrationRules.m"];
  Module[{v=D[u,x]/u},
  Log[u]*Log[a+b*x]/b -
  Dist[1/b,Int[Regularize[Log[a+b*x]*v,x],x]] /;
 RationalFunctionQ[v,x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[(a_.+b_.*x_)^m_.*Log[u_],x_Symbol] :=
(Print["Int(83th)@GeneralIntegrationRules.m"];
  Module[{v=D[u,x]/u},
  (a+b*x)^(m+1)*Log[u]/(b*(m+1)) -
  Dist[1/(b*(m+1)),Int[Regularize[(a+b*x)^(m+1)*v,x],x]]]) /;
FreeQ[{a,b,m},x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	FalseQ[PowerVariableExpn[u,m+1,x]]

(* ::Code:: *)
Int[v_*Log[u_],x_Symbol] :=
(Print["Int(84th)@GeneralIntegrationRules.m"];
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  w*Log[u] -
    Int[Regularize[w*D[u,x]/u,x],x] /;
 InverseFunctionFreeQ[w,x]]) /;
InverseFunctionFreeQ[u,x] && 
	Not[MatchQ[v, x^m_. /; FreeQ[m,x]]] &&
	FalseQ[FunctionOfLinear[v*Log[u],x]]

(* ::Code:: *)
Int[u_.*x_/(a_+b_.*x_^2),x_Symbol] :=
(Print["Int(85th)@GeneralIntegrationRules.m"];
  Module[{q=Rt[-a/b,2]},
  Dist[q/2,Int[u/(a+b*q*x),x]] -
  Dist[q/2,Int[u/(a-b*q*x),x]]]) /;
FreeQ[{a,b},x] && Not[MatchQ[u,r_*s_. /; SumQ[r]]] && Not[RationalFunctionQ[u,x]]

(* ::Code:: *)
Int[u_.*v_^m_./(a_+b_.*v_+c_.*w_),x_Symbol] :=
(Print["Int(86th)@GeneralIntegrationRules.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Dist[(1+b/q),Int[u*v^(m-1)/(b+q+2*c*v),x]] + Dist[(1-b/q),Int[u*v^(m-1)/(b-q+2*c*v),x]] /;
 NonzeroQ[q]]) /;
FreeQ[{a,b,c},x] && RationalQ[m] && m==1 && ZeroQ[w-v^2] && 
Not[MatchQ[u,r_*s_. /; SumQ[r]]] && (Not[RationalFunctionQ[u,x]] || Not[RationalFunctionQ[v,x]])

(* ::Code:: *)
Int[(d_.+e_.*v_)/(a_+b_.*v_+c_.*w_),x_Symbol] :=
(Print["Int(87th)@GeneralIntegrationRules.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
    Dist[e+(b*e-2*c*d)/q,Int[1/(b+q+2*c*v),x]] + Dist[e-(b*e-2*c*d)/q,Int[1/(b-q+2*c*v),x]] /;
 NonzeroQ[q]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[w-v^2] && NonzeroQ[2*c*d-b*e] && Not[RationalFunctionQ[v,x]]

(* ::Code:: *)
Int[u_./(a_+b_.*v_+c_.*w_),x_Symbol] :=
(Print["Int(88th)@GeneralIntegrationRules.m"];
  Module[{q=Rt[b^2-4*a*c,2]},
  Dist[2*c/q,Int[u/(b-q+2*c*v),x]] - Dist[2*c/q,Int[u/(b+q+2*c*v),x]] /;
 NonzeroQ[q]]) /;
FreeQ[{a,b,c},x] && ZeroQ[w-v^2] && Not[MatchQ[u,v^m_ /; RationalQ[m]]] &&
Not[MatchQ[u,r_*s_. /; SumQ[r]]] && (Not[RationalFunctionQ[u,x]] || Not[RationalFunctionQ[v,x]])

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(89th)@GeneralIntegrationRules.m"];
  Module[{v=SimplifyExpression[u,x]},
  Int[v,x] /;
 v=!=u ])

(* ::Code:: *)
Int[u_.*(v_^m_.*w_^n_.*t_^q_.)^p_,x_Symbol] :=
(Print["Int(90th)@GeneralIntegrationRules.m"];
  Int[u*v^(m*p)*w^(n*p)*t^(p*q),x]) /;
FreeQ[p,x] && Not[PowerQ[v]] && Not[PowerQ[w]] && Not[PowerQ[t]] &&
	ZeroQ[Simplify[(v^m*w^n*t^q)^p-v^(m*p)*w^(n*p)*t^(p*q)]]

(* ::Code:: *)
Int[u_.*(v_^m_.*w_^n_.*t_^q_.)^p_,x_Symbol] :=
(Print["Int(91th)@GeneralIntegrationRules.m"];
  Module[{r=Simplify[(v^m*w^n*t^q)^p/(v^(m*p)*w^(n*p)*t^(p*q))],lst},
  ( lst=SplitFreeFactors[v^(m*p)*w^(n*p)*t^(p*q),x];
  r*lst[[1]]*Int[Regularize[u*lst[[2]],x],x] ) /;
 NonzeroQ[r-1]]) /;
FreeQ[p,x] && Not[PowerQ[v] || PowerQ[w] || PowerQ[t] || FreeQ[v,x] || FreeQ[w,x] || FreeQ[t,x]]

(* ::Code:: *)
Int[u_*x_^m_./(a_+b_.*x_^n_),x_Symbol] :=
(Print["Int(92th)@GeneralIntegrationRules.m"];
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]]},
  Dist[r^(m+1)/(a*n*s^m), Sum[Int[u*(-1)^(2*k*(m+1)/n)/(r*(-1)^(2*k/n)-s*x),x],{k,1,n}]]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && 0<m<n && Not[AlgebraicFunctionQ[u,x]]

(* ::Code:: *)
Int[u_/(a_+b_.*x_^n_),x_Symbol] :=
(Print["Int(93th)@GeneralIntegrationRules.m"];
  Module[{r=Numerator[Rt[-a/b,n]], s=Denominator[Rt[-a/b,n]]},
  Dist[r/(a*n), Sum[Int[u*(-1)^(2*k/n)/(r*(-1)^(2*k/n)-s*x),x],{k,1,n}]]]) /;
FreeQ[{a,b},x] && OddQ[n] && n>1 && Not[AlgebraicFunctionQ[u,x]]

(* ::Code:: *)
Int[u_.*v_^m_/(a_+b_.*v_^n_),x_Symbol] :=
(Print["Int(94th)@GeneralIntegrationRules.m"];
  Dist[1/(b*n),Sum[Int[Together[u/(v-Rt[-a/b,n]*(-1)^(2*k/n))],x],{k,1,n}]]) /;
FreeQ[{a,b},x] && OddQ[n] && n>1 && ZeroQ[m-n+1] && 
  Not[AlgebraicFunctionQ[u,x] && AlgebraicFunctionQ[v,x]]

(* ::Code:: *)
Int[u_./(a_+b_.*v_^n_),x_Symbol] :=
(Print["Int(95th)@GeneralIntegrationRules.m"];
  Dist[1/(a*n),Sum[Int[Together[u/(1-v/(Rt[-a/b,n]*(-1)^(2*k/n)))],x],{k,1,n}]]) /;
FreeQ[{a,b},x] && OddQ[n] && n>1 && Not[AlgebraicFunctionQ[u,x] && AlgebraicFunctionQ[v,x]]

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(96th)@GeneralIntegrationRules.m"];
  Module[{v=ExpnExpand[u,x]},
  Int[v,x] /;
 v=!=u ])

(* ::Code:: *)
If[ShowSteps, 

Int[u_,x_Symbol] :=
(Print["Int(97th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForInverseLinear[u,x]},
  ShowStep["","Int[f[1/(a+b*x)],x]","-Subst[Int[f[x]/x^2,x],x,1/(a+b*x)]/b",Hold[
  -Dist[1/lst[[3]],Subst[Int[lst[[1]]/x^2,x],x,1/lst[[2]]]]]] /;
 NotFalseQ[lst]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(98th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForInverseLinear[u,x]},
  -Dist[1/lst[[3]],Subst[Int[lst[[1]]/x^2,x],x,1/lst[[2]]]] /;
 NotFalseQ[lst]])]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(99th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfLinear[u,x]},
  ShowStep["","Int[f[a+b*x],x]","Subst[Int[f[x],x],x,a+b*x]/b",Hold[
  Dist[1/lst[[3]],Subst[Int[lst[[1]],x],x,lst[[2]]+lst[[3]]*x]]]] /;
 Not[FalseQ[lst]]]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(100th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfLinear[u,x]},
  Dist[1/lst[[3]],Subst[Int[lst[[1]],x],x,lst[[2]]+lst[[3]]*x]] /;
 Not[FalseQ[lst]]])]

(* ::Code:: *)
Int[u_./(a_+b_.*v_^n_),x_Symbol] :=
(Print["Int(101th)@GeneralIntegrationRules.m"];
  Dist[2/(a*n),Sum[Int[Together[u/(1-v^2/(Rt[-a/b,n/2]*(-1)^(4*k/n)))],x],{k,1,n/2}]]) /;
FreeQ[{a,b},x] && EvenQ[n] && n>2

(* ::Code:: *)
Int[u_.*(a_+b_.*v_^n_)^m_,x_Symbol] :=
(Print["Int(102th)@GeneralIntegrationRules.m"];
  Dist[a^m,Int[u*Product[(1-(-1)^(4*k/n)*Rt[-b/a,n/2]*v^2)^m,{k,1,n/2}],x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-1 && EvenQ[n] && n>2 

(* ::Code:: *)
Int[u_.*(a_+b_.*v_^n_)^m_,x_Symbol] :=
(Print["Int(103th)@GeneralIntegrationRules.m"];
  Dist[a^m,Int[u*Product[(1+(-1)^(2*k/n)*Rt[b/a,n]*v)^m,{k,1,n}],x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m<-1 && OddQ[n] && n>1

(* ::Code:: *)
Int[u_.*(a_+b_.*v_+c_.*w_)^m_,x_Symbol] :=
(Print["Int(104th)@GeneralIntegrationRules.m"];
  Dist[1/(4*c)^m,Int[u*(b-Sqrt[b^2-4*a*c]+2*c*v)^m*(b+Sqrt[b^2-4*a*c]+2*c*v)^m,x]]) /;
FreeQ[{a,b,c},x] && IntegerQ[m] && m<0 && ZeroQ[w-v^2]

(* ::Code:: *)
Int[u_,x_Symbol] :=
(Print["Int(105th)@GeneralIntegrationRules.m"];
  Module[{v=NormalForm[u,x]},
  Int[v,x] /;
 Not[v===u]])

(* ::Code:: *)
Int[u_.*(a_.*v_^m_.)^p_, x_Symbol] :=
(Print["Int(106th)@GeneralIntegrationRules.m"];
  Module[{q=FractionalPart[p]},
  q=a^(p-q)*(a*v^m)^q/v^(m*q);
  If[FreeQ[Simplify[q],x],
    Simplify[q]*Int[u*v^(m*p),x],
  q*Int[u*v^(m*p),x]]]) /;
FreeQ[{a,m},x] && FractionQ[p] && Not[ZeroQ[a-1] && ZeroQ[m-1]]

(* ::Code:: *)
Int[u_.*(v_^m_)^p_,x_Symbol] :=
(Print["Int(107th)@GeneralIntegrationRules.m"];
  Simplify[(v^m)^p/v^(m*p)]*Int[Regularize[u*v^(m*p),x],x]) /;
FreeQ[p,x] && Not[PowerQ[v]]

(* ::Code:: *)
Int[u_.*(a_.*v_^m_.*w_^n_.)^p_, x_Symbol] :=
(Print["Int(108th)@GeneralIntegrationRules.m"];
  Module[{q=FractionalPart[p]},
  q=a^(p-q)*(a*v^m*w^n)^q/(v^(m*q)*w^(n*q));
  If[FreeQ[Simplify[q],x],
    Simplify[q]*Int[u*v^(m*p)*w^(n*p),x],
  q*Int[u*v^(m*p)*w^(n*p),x]]]) /;
FreeQ[a,x] && RationalQ[{m,n,p}]

(* ::Code:: *)
Int[u_.*(v_^m_.*w_^n_.)^p_,x_Symbol] :=
(Print["Int(109th)@GeneralIntegrationRules.m"];
  Module[{r=Simplify[(v^m*w^n)^p/(v^(m*p)*w^(n*p))],lst},
  If[ZeroQ[r-1],
    Int[u*v^(m*p)*w^(n*p),x],
  lst=SplitFreeFactors[v^(m*p)*w^(n*p),x];
  r*lst[[1]]*Int[Regularize[u*lst[[2]],x],x]]]) /;
FreeQ[p,x] && Not[PowerQ[v]] && Not[PowerQ[w]]

(* ::Code:: *)
Int[u_.*v_^m_*w_^n_,x_Symbol] :=
(Print["Int(110th)@GeneralIntegrationRules.m"];
  Module[{q=Cancel[v/w]},
  (v^m*w^n)/q^m*Int[u*q^m,x] /;
 PolynomialQ[q,x]]) /;
FractionQ[{m,n}] && m+n==0 && PolynomialQ[v,x] && PolynomialQ[w,x]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(111th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForFractionalPowerOfLinear[u,x]},
  ShowStep["","Int[f[(a+b*x)^(1/n),x],x]",
			"n/b*Subst[Int[x^(n-1)*f[x,-a/b+x^n/b],x],x,(a+b*x)^(1/n)]",Hold[
  Dist[lst[[2]]*lst[[4]],Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])]]]] /;
 NotFalseQ[lst]  ]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(112th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForFractionalPowerOfLinear[u,x]},
  Dist[lst[[2]]*lst[[4]],Subst[Int[lst[[1]],x],x,lst[[3]]^(1/lst[[2]])]] /;
 NotFalseQ[lst]  ])]

(* ::Code:: *)
Int[u_./(a_+b_.*v_^2),x_Symbol] :=
(Print["Int(113th)@GeneralIntegrationRules.m"];
  Dist[1/2,Int[u/(a+b*Rt[-a/b,2]*v),x]] + Dist[1/2,Int[u/(a-b*Rt[-a/b,2]*v),x]]) /;
FreeQ[{a,b},x] 

(* ::Code:: *)
Int[u_.*(a_+b_.*v_^2)^m_,x_Symbol] :=
(Print["Int(114th)@GeneralIntegrationRules.m"];
  Dist[a^m,Int[u*(1+Rt[-b/a,2]*v)^m*(1-Rt[-b/a,2]*v)^m,x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && (m<-1 || m==-1 && PositiveQ[-b/a])

(* ::Code:: *)
Int[u_.*f_^(a_+v_)*g_^(b_+w_),x_Symbol] :=
(Print["Int(115th)@GeneralIntegrationRules.m"];
  Dist[f^a*g^b,Int[u*f^v*g^w,x]]) /;
FreeQ[{a,b,f,g},x] && Not[MatchQ[v,c_+t_ /; FreeQ[c,x]]] && Not[MatchQ[w,c_+t_ /; FreeQ[c,x]]]

(* ::Code:: *)
Int[u_.*f_^(a_+v_),x_Symbol] :=
(Print["Int(116th)@GeneralIntegrationRules.m"];
  Dist[f^a,Int[u*f^v,x]]) /;
FreeQ[{a,f},x] && Not[MatchQ[v,b_+w_ /; FreeQ[b,x]]]

(* ::Code:: *)
Int[u_*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(117th)@GeneralIntegrationRules.m"];
  Sqrt[a+b*Sin[c+d*x]]/(Cos[c/2+d*x/2]+a/b*Sin[c/2+d*x/2])*
    (Int[u*Cos[c/2+d*x/2]*(a+b*Sin[c+d*x])^(n-1/2),x] +
     a/b*Int[u*Sin[c/2+d*x/2]*(a+b*Sin[c+d*x])^(n-1/2),x])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && IntegerQ[n-1/2]

(* ::Code:: *)
Int[u_*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(118th)@GeneralIntegrationRules.m"];
  Sqrt[a+b*Cos[c+d*x]]/Cos[c/2+d*x/2]*Int[u*Cos[c/2+d*x/2]*(a+b*Cos[c+d*x])^(n-1/2),x]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && IntegerQ[n-1/2]

(* ::Code:: *)
Int[u_*(a_+b_.*Cos[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(119th)@GeneralIntegrationRules.m"];
  Sqrt[a+b*Cos[c+d*x]]/Sin[c/2+d*x/2]*Int[u*Sin[c/2+d*x/2]*(a+b*Cos[c+d*x])^(n-1/2),x]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b] && IntegerQ[n-1/2]

(* ::Code:: *)
Int[u_*(a_+b_.*Cos[d_.+e_.*x_]+c_.*Sin[d_.+e_.*x_])^n_,x_Symbol] :=
(Print["Int(120th)@GeneralIntegrationRules.m"];
  Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(c*Cos[d/2+e*x/2]+(a-b)*Sin[d/2+e*x/2])*
    Dist[c,Int[u*Cos[d/2+e*x/2]*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1/2),x]] + 
  Sqrt[a+b*Cos[d+e*x]+c*Sin[d+e*x]]/(c*Cos[d/2+e*x/2]+(a-b)*Sin[d/2+e*x/2])*
    Dist[a-b,Int[u*Sin[d/2+e*x/2]*(a+b*Cos[d+e*x]+c*Sin[d+e*x])^(n-1/2),x]]) /;
FreeQ[{a,b,c,d,e},x] && ZeroQ[a^2-b^2-c^2] && IntegerQ[n-1/2]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(121th)@GeneralIntegrationRules.m"];
  ShowStep["","Int[f[Sin[x],Cos[x]],x]",
			"2*Subst[Int[f[2*x/(1+x^2),(1-x^2)/(1+x^2)]/(1+x^2),x],x,Tan[x/2]]",Hold[
  Dist[2,
   Subst[Int[Regularize[SubstForTrig[u,2*x/(1+x^2),(1-x^2)/(1+x^2),x,x]/(1+x^2),x],x],x,Tan[x/2]]]]]) /;
SimplifyFlag && FunctionOfTrigQ[u,x,x],

Int[u_,x_Symbol] :=
(Print["Int(122th)@GeneralIntegrationRules.m"];
  Dist[2,
   Subst[Int[Regularize[SubstForTrig[u,2*x/(1+x^2),(1-x^2)/(1+x^2),x,x]/(1+x^2),x],x],x,Tan[x/2]]]) /;
FunctionOfTrigQ[u,x,x]]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(123th)@GeneralIntegrationRules.m"];
  ShowStep["","Int[f[Sinh[x],Cosh[x]],x]",
			"2*Subst[Int[f[2*x/(1-x^2),(1+x^2)/(1-x^2)]/(1-x^2),x],x,Tanh[x/2]]",Hold[
  Dist[2,
   Subst[Int[Regularize[SubstForHyperbolic[u,2*x/(1-x^2),(1+x^2)/(1-x^2),x,x]/(1-x^2),x],x],x,Tanh[x/2]]]]]) /;
SimplifyFlag && FunctionOfHyperbolicQ[u,x,x],

Int[u_,x_Symbol] :=
(Print["Int(124th)@GeneralIntegrationRules.m"];
  Dist[2,
   Subst[Int[Regularize[SubstForHyperbolic[u,2*x/(1-x^2),(1+x^2)/(1-x^2),x,x]/(1-x^2),x],x],x,Tanh[x/2]]]) /;
FunctionOfHyperbolicQ[u,x,x]]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(125th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfSquareRootOfQuadratic[u,x]},
  ShowStep["","Int[f[Sqrt[a+b*x+c*x^2],x],x]",
			"2*Subst[Int[f[(c*Sqrt[a]-b*x+Sqrt[a]*x^2)/(c-x^2),(-b+2*Sqrt[a]*x)/(c-x^2)]*
				(c*Sqrt[a]-b*x+Sqrt[a]*x^2)/(c-x^2)^2,x],x,(-Sqrt[a]+Sqrt[a+b*x+c*x^2])/x]",
			Hold[Dist[2,Subst[Int[lst[[1]],x],x,lst[[2]]]]]] /;
 Not[FalseQ[lst]] && lst[[3]]===1]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(126th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfSquareRootOfQuadratic[u,x]},
  Dist[2,Subst[Int[lst[[1]],x],x,lst[[2]]]] /;
 Not[FalseQ[lst]]])]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(127th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfSquareRootOfQuadratic[u,x]},
  ShowStep["","Int[f[Sqrt[a+b*x+c*x^2],x],x]",
			"2*Subst[Int[f[(a*Sqrt[c]+b*x+Sqrt[c]*x^2)/(b+2*Sqrt[c]*x),(-a+x^2)/(b+2*Sqrt[c]*x)]*
				(a*Sqrt[c]+b*x+Sqrt[c]*x^2)/(b+2*Sqrt[c]*x)^2,x],x,Sqrt[c]*x+Sqrt[a+b*x+c*x^2]]",
			Hold[Dist[2,Subst[Int[lst[[1]],x],x,lst[[2]]]]]] /;
 Not[FalseQ[lst]] && lst[[3]]===2]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(128th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfSquareRootOfQuadratic[u,x]},
  Dist[2,Subst[Int[lst[[1]],x],x,lst[[2]]]] /;
 Not[FalseQ[lst]]])]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(129th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfSquareRootOfQuadratic[u,x]},
  ShowStep["","Int[f[Sqrt[a+b*x+c*x^2],x],x]",
		   "-2*Sqrt[b^2-4*a*c]*Subst[Int[f[-Sqrt[b^2-4*a*c]*x/(c-x^2),
			  (b*c+c*Sqrt[b^2-4*a*c]+(-b+Sqrt[b^2-4*a*c])*x^2)/(-2*c*(c-x^2))]*x/(c-x^2)^2,x],
			   x,2*c*Sqrt[a+b*x+c*x^2]/(b-Sqrt[b^2-4*a*c]+2*c*x)]",
		   Hold[Dist[2,Subst[Int[lst[[1]],x],x,lst[[2]]]]]] /;
 Not[FalseQ[lst]] && lst[[3]]===3]) /;
SimplifyFlag,

Int[u_,x_Symbol] :=
(Print["Int(130th)@GeneralIntegrationRules.m"];
  Module[{lst=FunctionOfSquareRootOfQuadratic[u,x]},
  Dist[2,Subst[Int[lst[[1]],x],x,lst[[2]]]] /;
 Not[FalseQ[lst]]])]

(* ::Code:: *)
Int[u_*(1-(a_.+b_.*x_)^2)^n_.,x_Symbol] :=
(Print["Int(131th)@GeneralIntegrationRules.m"];
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  Dist[1/b,Subst[Int[Regularize[SubstForInverseFunction[u,tmp,x]*Cos[x]^(2*n+1),x],x],x,tmp]] /;
 NotFalseQ[tmp] && tmp===ArcSin[a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[2*n]

(* ::Code:: *)
Int[u_*(1-(a_.+b_.*x_)^2)^n_.,x_Symbol] :=
(Print["Int(132th)@GeneralIntegrationRules.m"];
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  -Dist[1/b,Subst[Int[Regularize[SubstForInverseFunction[u,tmp,x]*Sin[x]^(2*n+1),x],x],x,tmp]] /;
 NotFalseQ[tmp] && tmp===ArcCos[a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[2*n]

(* ::Code:: *)
Int[u_*(1+(a_.+b_.*x_)^2)^n_.,x_Symbol] :=
(Print["Int(133th)@GeneralIntegrationRules.m"];
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  Dist[1/b,Subst[Int[Regularize[SubstForInverseFunction[u,tmp,x]*Cosh[x]^(2*n+1),x],x],x,tmp]] /;
 NotFalseQ[tmp] && tmp===ArcSinh[a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[2*n]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(134th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForInverseFunctionOfLinear[u,x]},
  ShowStep["If h[g[x]]==x","Int[f[x,g[a+b*x]],x]",
	"Subst[Int[f[-a/b+h[x]/b,x]*h'[x],x],x,g[a+b*x]]/b",Hold[
  Dist[1/lst[[3]],Subst[Int[lst[[1]],x],x,lst[[2]]]]]] /;
 NotFalseQ[lst]]) /;
SimplifyFlag && Not[NotIntegrableQ[u,x]],

Int[u_,x_Symbol] :=
(Print["Int(135th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForInverseFunctionOfLinear[u,x]},
  Dist[1/lst[[3]],Subst[Int[lst[[1]],x],x,lst[[2]]]] /;
 NotFalseQ[lst]]) /;
Not[NotIntegrableQ[u,x]]]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(136th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForInverseFunctionOfQuotientOfLinears[u,x]},
  ShowStep["If h[g[x]]==x","Int[f[x,g[(a+b*x)/(c+d*x)]],x]",
"(b*c-a*d)*Subst[Int[f[(-a+c*h[x])/(b-d*h[x]),x]*h'[x]/(b-d*h[x])^2,x],x,g[(a+b*x)/(c+d*x)]]",Hold[
  Dist[lst[[3]],Subst[Int[lst[[1]],x],x,lst[[2]]]]]] /;
 NotFalseQ[lst]]) /;
SimplifyFlag && Not[NotIntegrableQ[u,x]],

Int[u_,x_Symbol] :=
(Print["Int(137th)@GeneralIntegrationRules.m"];
  Module[{lst=SubstForInverseFunctionOfQuotientOfLinears[u,x]},
  Dist[lst[[3]],Subst[Int[lst[[1]],x],x,lst[[2]]]] /;
 NotFalseQ[lst]]) /;
Not[NotIntegrableQ[u,x]]]

