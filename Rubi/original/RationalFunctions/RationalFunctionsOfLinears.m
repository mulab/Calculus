(* ::Package:: *)

(* ::Code:: *)
Int[a_,x_Symbol] :=
(Print["Int(1th)@RationalFunctionsOfLinears.m"];
   a*x) /;
IndependentQ[a,x]

(* ::Code:: *)
Int[c_*(a_+b_.*x_),x_Symbol] :=
(Print["Int(2th)@RationalFunctionsOfLinears.m"];
  c*(a+b*x)^2/(2*b)) /;
FreeQ[{a,b,c},x]

(* ::Code:: *)
Int[c_*(a_+b_.*x_)^n_,x_Symbol] :=
(Print["Int(3th)@RationalFunctionsOfLinears.m"];
  Dist[c,Int[(a+b*x)^n,x]]) /;
FreeQ[{a,b,c,n},x] && NonzeroQ[n+1]

(* ::Code:: *)
If[ShowSteps,

Int[a_*u_,x_Symbol] :=
(Print["Int(4th)@RationalFunctionsOfLinears.m"];
  Module[{lst=ConstantFactor[u,x]},
  ShowStep["","Int[a*u,x]","a*Int[u,x]",Hold[
  Dist[a*lst[[1]],Int[lst[[2]],x]]]]]) /;
SimplifyFlag && FreeQ[a,x] && Not[MatchQ[u,b_*v_ /; FreeQ[b,x]]],

Int[a_*u_,x_Symbol] :=
(Print["Int(5th)@RationalFunctionsOfLinears.m"];
  Module[{lst=ConstantFactor[u,x]},
  Dist[a*lst[[1]],Int[lst[[2]],x]]]) /;
FreeQ[a,x] && Not[MatchQ[u,b_*v_ /; FreeQ[b,x]]]]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(6th)@RationalFunctionsOfLinears.m"];
  Module[{lst=ConstantFactor[Simplify[Denominator[u]],x]},
  ShowStep["","Int[a*u,x]","a*Int[u,x]",Hold[
  Dist[1/lst[[1]],Int[Numerator[u]/lst[[2]],x]]]] /;
 lst[[1]]=!=1]) /;
SimplifyFlag && (
	MatchQ[u,1/(a_+b_.*x) /; FreeQ[{a,b},x]] ||
	MatchQ[u,x^m_./(a_+b_.*x^n_) /; FreeQ[{a,b,m,n},x] && ZeroQ[m-n+1]] ||
	MatchQ[u,1/((a_.+b_.*x)*(c_+d_.*x)) /; FreeQ[{a,b,c,d},x]] ||
	MatchQ[u,(d_.+e_.*x)/(a_+b_.*x+c_.*x^2) /; FreeQ[{a,b,c,d,e},x]] ||
	MatchQ[u,(c_.*(a_.+b_.*x)^n_)^m_ /; FreeQ[{a,b,c,m,n},x] && ZeroQ[m*n+1]]),

Int[u_,x_Symbol] :=
(Print["Int(7th)@RationalFunctionsOfLinears.m"];
  Module[{lst=ConstantFactor[Simplify[Denominator[u]],x]},
  Dist[1/lst[[1]],Int[Numerator[u]/lst[[2]],x]] /;
 lst[[1]]=!=1]) /;
	MatchQ[u,1/(a_+b_.*x) /; FreeQ[{a,b},x]] ||
	MatchQ[u,x^m_./(a_+b_.*x^n_) /; FreeQ[{a,b,m,n},x] && ZeroQ[m-n+1]] ||
	MatchQ[u,1/((a_.+b_.*x)*(c_+d_.*x)) /; FreeQ[{a,b,c,d},x]] ||
	MatchQ[u,(d_.+e_.*x)/(a_+b_.*x+c_.*x^2) /; FreeQ[{a,b,c,d,e},x]] ||
	MatchQ[u,(c_.*(a_.+b_.*x)^n_)^m_ /; FreeQ[{a,b,c,m,n},x] && ZeroQ[m*n+1]]]

(* ::Code:: *)
If[ShowSteps,

Int[u_/v_,x_Symbol] :=
(Print["Int(8th)@RationalFunctionsOfLinears.m"];
  Module[{lst=ConstantFactor[v,x]},
  ShowStep["","Int[a*u,x]","a*Int[u,x]",Hold[
  Dist[1/lst[[1]],Int[u/lst[[2]],x]]]] /;
 lst[[1]]=!=1]) /;
SimplifyFlag && Not[FalseQ[DerivativeDivides[v,u,x]]],

Int[u_/v_,x_Symbol] :=
(Print["Int(9th)@RationalFunctionsOfLinears.m"];
  Module[{lst=ConstantFactor[v,x]},
  Dist[1/lst[[1]],Int[u/lst[[2]],x]] /;
 lst[[1]]=!=1]) /;
Not[FalseQ[DerivativeDivides[v,u,x]]]]

(* ::Code:: *)
Int[u_.*v_^m_*w_^n_,x_Symbol] :=
(Print["Int(10th)@RationalFunctionsOfLinears.m"];
  (v^m*w^n)*Int[u,x]) /;
FreeQ[{m,n},x] && ZeroQ[m+n] && ZeroQ[v+w]

(* ::Code:: *)
Int[u_.*(a_.+b_.*x_^m_.)^p_.*(c_.+d_.*x_^n_.)^q_., x_Symbol] :=
(Print["Int(11th)@RationalFunctionsOfLinears.m"];
  (a+b*x^m)^p*(c+d*x^n)^q/x^(m*p)*Int[u*x^(m*p),x]) /;
FreeQ[{a,b,c,d,m,n,p,q},x] && ZeroQ[a+d] && ZeroQ[b+c] && ZeroQ[m+n] && ZeroQ[p+q]

(* ::Code:: *)
Int[1/(a_+b_.*x_),x_Symbol] :=
(Print["Int(12th)@RationalFunctionsOfLinears.m"];
  Log[-a-b*x]/b) /;
FreeQ[{a,b},x] && NegativeCoefficientQ[a]

(* ::Code:: *)
Int[1/(a_.+b_.*x_),x_Symbol] :=
(Print["Int(13th)@RationalFunctionsOfLinears.m"];
  Log[a+b*x]/b) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^n_.,x_Symbol] :=
(Print["Int(14th)@RationalFunctionsOfLinears.m"];
  x^(n+1)/(n+1)) /;
IndependentQ[n,x] && NonzeroQ[n+1]

(* ::Code:: *)
Int[(a_.+b_.*x_)^n_,x_Symbol] :=
(Print["Int(15th)@RationalFunctionsOfLinears.m"];
  (a+b*x)^(n+1)/(b*(n+1))) /;
FreeQ[{a,b,n},x] && NonzeroQ[n+1]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(16th)@RationalFunctionsOfLinears.m"];
  If[PolynomialQ[u,x],
    ShowStep["","Int[a+b*x+c*x^2+\[CenterEllipsis],x]","a*x+b*x^2/2+c*x^3/3+\[CenterEllipsis]",Hold[
    IntegrateMonomialSum[u,x]]],
  ShowStep["","Int[a+b/x+c*x^m+\[CenterEllipsis],x]","a*x+b*Log[x]+c*x^(m+1)/(m+1)+\[CenterEllipsis]",Hold[
  IntegrateMonomialSum[u,x]]]]) /;
SimplifyFlag && MonomialSumQ[u,x],

Int[u_,x_Symbol] :=
(Print["Int(17th)@RationalFunctionsOfLinears.m"];
  IntegrateMonomialSum[u,x]) /;
MonomialSumQ[u,x]]

(* ::Code:: *)
If[ShowSteps,

Int[u_,x_Symbol] :=
(Print["Int(18th)@RationalFunctionsOfLinears.m"];
  Module[{lst=SplitMonomialTerms[u,x]},
  ShowStep["","Int[a*u+b*v+\[CenterEllipsis],x]","a*Int[u,x]+b*Int[v,x]+\[CenterEllipsis]",Hold[
  Int[lst[[1]],x] + SplitFreeIntegrate[lst[[2]],x]]] /;
 SumQ[lst[[1]]] && Not[FreeQ[lst[[1]],x]] && lst[[2]]=!=0]) /;
SimplifyFlag && SumQ[u],

Int[u_,x_Symbol] :=
(Print["Int(19th)@RationalFunctionsOfLinears.m"];
  Module[{lst=SplitMonomialTerms[u,x]},
  Int[lst[[1]],x] + SplitFreeIntegrate[lst[[2]],x] /;
 SumQ[lst[[1]]] && Not[FreeQ[lst[[1]],x]] && lst[[2]]=!=0]) /;
SumQ[u]]

(* ::Code:: *)
If[ShowSteps,

Int[x_^m_.*u_,x_Symbol] :=
(Print["Int(20th)@RationalFunctionsOfLinears.m"];
  ShowStep["","Int[\!\(\*SuperscriptBox[\"x\", \"m\"]\)*(u+v+\[CenterEllipsis]),x]","Int[\!\(\*SuperscriptBox[\"x\", \"m\"]\)*u+\!\(\*SuperscriptBox[\"x\", \"m\"]\)*v+\[CenterEllipsis],x]",Hold[
  Int[Map[Function[x^m*#],u],x]]]) /;
SimplifyFlag && IntegerQ[m] && SumQ[u],

Int[x_^m_.*u_,x_Symbol] :=
(Print["Int(21th)@RationalFunctionsOfLinears.m"];
  Int[Map[Function[x^m*#],u],x]) /;
IntegerQ[m] && SumQ[u]]

(* ::Code:: *)
Int[1/(x_*(a_+b_.*x_^n_.)),x_Symbol] :=
(Print["Int(22th)@RationalFunctionsOfLinears.m"];
  -2*ArcTanh[1+2*b*x^n/a]/(a*n)) /;
FreeQ[{a,b,n},x] && PosQ[n] && (RationalQ[a] || RationalQ[b/a])

(* ::Code:: *)
Int[1/(x_*(a_+b_.*x_^n_.)),x_Symbol] :=
(Print["Int(23th)@RationalFunctionsOfLinears.m"];
  Log[x]/a - Log[a+b*x^n]/(a*n)) /;
FreeQ[{a,b,n},x] && PosQ[n] && Not[RationalQ[a] || RationalQ[b/a]]

(* ::Code:: *)
Int[1/(x_*(a_+b_.*x_^n_.)),x_Symbol] :=
(Print["Int(24th)@RationalFunctionsOfLinears.m"];
  -Log[b+a*x^(-n)]/(a*n)) /;
FreeQ[{a,b,n},x] && NegQ[n]

(* ::Code:: *)
Int[1/(a_.*x_+b_.*x_^n_),x_Symbol] :=
(Print["Int(25th)@RationalFunctionsOfLinears.m"];
  Int[1/(x*(a+b*x^(n-1))),x]) /;
FreeQ[{a,b,n},x]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_)^n_,x_Symbol] :=
(Print["Int(26th)@RationalFunctionsOfLinears.m"];
  -x^(m+1)*(a+b*x)^(n+1)/(a*(n+1))) /;
FreeQ[{a,b,m,n},x] && ZeroQ[m+n+2] && NonzeroQ[n+1]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_)^n_,x_Symbol] :=
(Print["Int(27th)@RationalFunctionsOfLinears.m"];
  -x^(m+1)*(a+b*x)^(n+1)/(a*(n+1)) +
  Dist[(m+n+2)/(a*(n+1)),Int[x^m*(a+b*x)^(n+1),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && 0<m<-n-2 && 2*m+n+1>0

(* ::Code:: *)
Int[x_^m_*(a_.+b_.*x_)^n_.,x_Symbol] :=
(Print["Int(28th)@RationalFunctionsOfLinears.m"];
  x^(m+1)*(a+b*x)^n/(m+n+1) +
  Dist[a*n/(m+n+1),Int[x^m*(a+b*x)^(n-1),x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && 0<n<m/2

(* ::Code:: *)
Int[x_^m_*(a_.+b_.*x_)^n_.,x_Symbol] :=
(Print["Int(29th)@RationalFunctionsOfLinears.m"];
  x^(m+1)*(a+b*x)^(n+1)/(a*(m+1)) -
  Dist[b*(m+n+2)/(a*(m+1)),Int[x^(m+1)*(a+b*x)^n,x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && 0<n<-m-2 && m+2*n-1>0

(* ::Code:: *)
Int[x_^m_.*(a_.+b_.*x_)^n_,x_Symbol] :=
(Print["Int(30th)@RationalFunctionsOfLinears.m"];
  x^m*(a+b*x)^(n+1)/(b*(m+n+1)) -
  Dist[a*m/(b*(m+n+1)),Int[x^(m-1)*(a+b*x)^n,x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && 0<m<n/2

(* ::Code:: *)
Int[(a_+b_.*x_)^n_.*(c_+d_.*x_)^n_.,x_Symbol] :=
(Print["Int(31th)@RationalFunctionsOfLinears.m"];
  Int[(a*c+b*d*x^2)^n,x]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && ZeroQ[b*c+a*d]

(* ::Code:: *)
Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_.,x_Symbol] :=
(Print["Int(32th)@RationalFunctionsOfLinears.m"];
  Dist[(d/b)^n,Int[(a+b*x)^(m+n),x]]) /;
FreeQ[{a,b,c,d,m},x] && ZeroQ[b*c-a*d] && IntegerQ[n] && 
(Not[IntegerQ[m]] || LeafCount[a+b*x]<=LeafCount[c+d*x])

(* ::Code:: *)
Int[1/((a_+b_.*x_)*(c_+d_.*x_)),x_Symbol] :=
(Print["Int(33th)@RationalFunctionsOfLinears.m"];
  -2*ArcTanh[(b*c+a*d)/(b*c-a*d) + 2*b*d*x/(b*c-a*d)]/(b*c-a*d)) /;
FreeQ[{a,b,c,d},x] && RationalQ[b*c-a*d] && b*c-a*d!=0

(* ::Code:: *)
Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_,x_Symbol] :=
(Print["Int(34th)@RationalFunctionsOfLinears.m"];
  -(a+b*x)^(m+1)*(c+d*x)^(n+1)/((n+1)*(b*c-a*d))) /;
FreeQ[{a,b,c,d,m,n},x] && ZeroQ[m+n+2] && NonzeroQ[b*c-a*d] && NonzeroQ[n+1]

(* ::Code:: *)
Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_,x_Symbol] :=
(Print["Int(35th)@RationalFunctionsOfLinears.m"];
  -(a+b*x)^(m+1)*(c+d*x)^(n+1)/((n+1)*(b*c-a*d)) +
  Dist[b*(m+n+2)/((n+1)*(b*c-a*d)),Int[(a+b*x)^m*(c+d*x)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && IntegersQ[m,n] && NonzeroQ[b*c-a*d] && 0<m<-n-2 && 2*m+n+1>0

(* ::Code:: *)
Int[(a_+b_.*x_)^m_*(c_+d_.*x_)^n_.,x_Symbol] :=
(Print["Int(36th)@RationalFunctionsOfLinears.m"];
  (a+b*x)^(m+1)*(c+d*x)^n/(b*(m+n+1)) +
  Dist[n*(b*c-a*d)/(b*(m+n+1)),Int[(a+b*x)^m*(c+d*x)^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && IntegersQ[m,n] && NonzeroQ[b*c-a*d] && 0<n<=m

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_)^n_.*(c_+d_.*x_)^n_.,x_Symbol] :=
(Print["Int(37th)@RationalFunctionsOfLinears.m"];
  Int[x^m*(a*c+b*d*x^2)^n,x]) /;
FreeQ[{a,b,c,d,m},x] && IntegerQ[n] && ZeroQ[b*c+a*d]

(* ::Code:: *)
Int[(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.), x_Symbol] :=
(Print["Int(38th)@RationalFunctionsOfLinears.m"];
  c*x*(a+b*x^n)^(p+1)/a) /;
FreeQ[{a,b,c,d,n,p},x] && ZeroQ[a*d-b*c*(n*(p+1)+1)]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_+d_.*x_^n_.), x_Symbol] :=
(Print["Int(39th)@RationalFunctionsOfLinears.m"];
  c*x^(m+1)*(a+b*x^n)^(p+1)/(a*(m+1))) /;
FreeQ[{a,b,c,d,m,n,p},x] && NonzeroQ[m+1] && ZeroQ[a*d*(m+1)-b*c*(m+n*(p+1)+1)]

(* ::Code:: *)
Int[x_^m_.*(a_+b_.*x_^n_.)^p_.*(c_.*x_^q_.+d_.*x_^r_.), x_Symbol] :=
(Print["Int(40th)@RationalFunctionsOfLinears.m"];
  c*x^(m+q+1)*(a+b*x^n)^(p+1)/(a*(m+q+1))) /;
FreeQ[{a,b,c,d,m,n,p,q,r},x] && ZeroQ[r-n-q] && NonzeroQ[m+q+1] && 
	ZeroQ[a*d*(m+q+1)-b*c*(m+q+n*(p+1)+1)]

(* ::Code:: *)
Int[(a_+b_.*x_)^m_.*(c_+d_.*x_)^n_.*(e_+f_.*x_), x_Symbol] :=
(Print["Int(41th)@RationalFunctionsOfLinears.m"];
  f*(a+b*x)^(m+1)*(c+d*x)^(n+1)/(b*d*(m+n+2))) /;
FreeQ[{a,b,c,d,e,f,m,n},x] && NonzeroQ[m+n+2] && ZeroQ[f*(b*c*(m+1)+a*d*(n+1))-b*d*e*(m+n+2)]

(* ::Code:: *)
Int[x_*(a_+b_.*x_)^n_.*(c_+d_.*x_)^p_.,x_Symbol] :=
(Print["Int(42th)@RationalFunctionsOfLinears.m"];
  (a+b*x)^(n+1)*(c+d*x)^(p+1)/(b*d*(2+n+p)) -
  Dist[(b*c*(n+1)+a*d*(p+1))/(b*d*(2+n+p)), Int[(a+b*x)^n*(c+d*x)^p, x]]) /;
FreeQ[{a,b,c,d,n,p},x] && IntegersQ[n,p] && 0<n<=2 && p>5

(* ::Code:: *)
Int[x_^m_*(a_+b_.*x_)^n_.*(c_+d_.*x_)^p_.,x_Symbol] :=
(Print["Int(43th)@RationalFunctionsOfLinears.m"];
  x^(m-1)*(a+b*x)^(n+1)*(c+d*x)^(p+1)/(b*d*(1+m+n+p)) -
  Dist[a*c*(m-1)/(b*d*(1+m+n+p)), Int[x^(m-2)*(a+b*x)^n*(c+d*x)^p, x]] -
  Dist[(b*c*(m+n)+a*d*(m+p))/(b*d*(1+m+n+p)), Int[x^(m-1)*(a+b*x)^n*(c+d*x)^p, x]]) /;
FreeQ[{a,b,c,d,n,p},x] && IntegersQ[m,n,p] && 0<m<=2 && 0<n<=2 && p>5
