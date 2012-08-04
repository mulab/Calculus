(* ::Package:: *)

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_],x_Symbol] :=
(Print["Int(1th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Sinh[c+d*x]/(d^2-b^2*p^2*Log[f]^2) + 
  d*(f^(a+b*x))^p*Cosh[c+d*x]/(d^2-b^2*p^2*Log[f]^2)) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2-b^2*p^2*Log[f]^2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_],x_Symbol] :=
(Print["Int(2th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Cosh[c+d*x]/(d^2-b^2*p^2*Log[f]^2) + 
  d*(f^(a+b*x))^p*Sinh[c+d*x]/(d^2-b^2*p^2*Log[f]^2)) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2-b^2*p^2*Log[f]^2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(3th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Sinh[c+d*x]^n/(d^2*n^2-b^2*p^2*Log[f]^2) + 
  d*n*(f^(a+b*x))^p*Cosh[c+d*x]*Sinh[c+d*x]^(n-1)/(d^2*n^2-b^2*p^2*Log[f]^2) - 
  Dist[n*(n-1)*d^2/(d^2*n^2-b^2*p^2*Log[f]^2),Int[(f^(a+b*x))^p*Sinh[c+d*x]^(n-2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*n^2-b^2*p^2*Log[f]^2] && RationalQ[n] && n>1

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(4th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Cosh[c+d*x]^n/(d^2*n^2-b^2*p^2*Log[f]^2) + 
  d*n*(f^(a+b*x))^p*Sinh[c+d*x]*Cosh[c+d*x]^(n-1)/(d^2*n^2-b^2*p^2*Log[f]^2) + 
  Dist[n*(n-1)*d^2/(d^2*n^2-b^2*p^2*Log[f]^2),Int[(f^(a+b*x))^p*Cosh[c+d*x]^(n-2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*n^2-b^2*p^2*Log[f]^2] && RationalQ[n] && n>1

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(5th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Sinh[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) + 
  (f^(a+b*x))^p*Cosh[c+d*x]*Sinh[c+d*x]^(n+1)/(d*(n+1))) /;
FreeQ[{a,b,c,d,f,n,p},x] && ZeroQ[d^2*(n+2)^2-b^2*p^2*Log[f]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(6th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  b*p*Log[f]*(f^(a+b*x))^p*Cosh[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) - 
  (f^(a+b*x))^p*Sinh[c+d*x]*Cosh[c+d*x]^(n+1)/(d*(n+1))) /;
FreeQ[{a,b,c,d,f,n,p},x] && ZeroQ[d^2*(n+2)^2-b^2*p^2*Log[f]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(7th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Sinh[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) + 
  (f^(a+b*x))^p*Cosh[c+d*x]*Sinh[c+d*x]^(n+1)/(d*(n+1)) - 
  Dist[(d^2*(n+2)^2-b^2*p^2*Log[f]^2)/(d^2*(n+1)*(n+2)),Int[(f^(a+b*x))^p*Sinh[c+d*x]^(n+2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*(n+2)^2-b^2*p^2*Log[f]^2] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(8th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  b*p*Log[f]*(f^(a+b*x))^p*Cosh[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) - 
  (f^(a+b*x))^p*Sinh[c+d*x]*Cosh[c+d*x]^(n+1)/(d*(n+1)) + 
  Dist[(d^2*(n+2)^2-b^2*p^2*Log[f]^2)/(d^2*(n+1)*(n+2)),Int[(f^(a+b*x))^p*Cosh[c+d*x]^(n+2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*(n+2)^2-b^2*p^2*Log[f]^2] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sech[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(9th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  b*p*Log[f]*(f^(a+b*x))^p*Sech[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) + 
  (f^(a+b*x))^p*Sech[c+d*x]^(n-1)*Sinh[c+d*x]/(d*(n-1))) /;
FreeQ[{a,b,c,d,f,p,n},x] && ZeroQ[b^2*p^2*Log[f]^2-d^2*(n-2)^2] && NonzeroQ[n-1] && NonzeroQ[n-2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Csch[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(10th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Csch[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) - 
  (f^(a+b*x))^p*Csch[c+d*x]^(n-1)*Cosh[c+d*x]/(d*(n-1))) /;
FreeQ[{a,b,c,d,f,p,n},x] && ZeroQ[b^2*p^2*Log[f]^2-d^2*(n-2)^2] && NonzeroQ[n-1] && NonzeroQ[n-2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sech[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(11th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  b*p*Log[f]*(f^(a+b*x))^p*Sech[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) + 
  (f^(a+b*x))^p*Sech[c+d*x]^(n-1)*Sinh[c+d*x]/(d*(n-1)) -
  Dist[(b^2*p^2*Log[f]^2-d^2*(n-2)^2)/(d^2*(n-1)*(n-2)),
    Int[(f^(a+b*x))^p*Sech[c+d*x]^(n-2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[b^2*p^2*Log[f]^2-d^2*(n-2)^2] && 
  RationalQ[n] && n>1 && n!=2

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Csch[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(12th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Csch[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) - 
  (f^(a+b*x))^p*Csch[c+d*x]^(n-1)*Cosh[c+d*x]/(d*(n-1)) +
  Dist[(b^2*p^2*Log[f]^2-d^2*(n-2)^2)/(d^2*(n-1)*(n-2)),
    Int[(f^(a+b*x))^p*Csch[c+d*x]^(n-2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[b^2*p^2*Log[f]^2-d^2*(n-2)^2] && 
  RationalQ[n] && n>1 && n!=2

(* ::Code:: *)
Int[x_^m_.*(f_^(a_.+b_.*x_))^p_.*Sinh[c_.+d_.*x_]^n_.,x_Symbol] :=
(Print["Int(13th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(f^(a+b*x))^p*Sinh[c+d*x]^n,x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]]) /;
FreeQ[{a,b,c,d,f,p},x] && RationalQ[m] && m>0 && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_.*(f_^(a_.+b_.*x_))^p_.*Cosh[c_.+d_.*x_]^n_.,x_Symbol] :=
(Print["Int(14th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(f^(a+b*x))^p*Cosh[c+d*x]^n,x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]]) /;
FreeQ[{a,b,c,d,f,p},x] && RationalQ[m] && m>0 && IntegerQ[n] && n>0

(* ::Code:: *)
Int[f_^v_*Sinh[w_],x_Symbol] :=
(Print["Int(15th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  Dist[1/2,Int[f^v*E^w,x]] - 
  Dist[1/2,Int[f^v/E^w,x]]) /;
FreeQ[f,x] && PolynomialQ[v,x] && Exponent[v,x]<=2 && PolynomialQ[w,x] && Exponent[w,x]<=2

(* ::Code:: *)
Int[f_^v_*Cosh[w_],x_Symbol] :=
(Print["Int(16th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  Dist[1/2,Int[f^v*E^w,x]] + 
  Dist[1/2,Int[f^v/E^w,x]]) /;
FreeQ[f,x] && PolynomialQ[v,x] && Exponent[v,x]<=2 && PolynomialQ[w,x] && Exponent[w,x]<=2

(* ::Code:: *)
Int[f_^v_*Sinh[w_]^n_,x_Symbol] :=
(Print["Int(17th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  Dist[1/2^n,Int[f^v*(E^w-1/E^w)^n,x]]) /;
FreeQ[f,x] && IntegerQ[n] && n>0 && PolynomialQ[v,x] && Exponent[v,x]<=2 && 
  PolynomialQ[w,x] && Exponent[w,x]<=2

(* ::Code:: *)
Int[f_^v_*Cosh[w_]^n_,x_Symbol] :=
(Print["Int(18th)@ProductsOfExponentialAndHyperbolicFunctions.m"];
  Dist[1/2^n,Int[f^v*(E^w+1/E^w)^n,x]]) /;
FreeQ[f,x] && IntegerQ[n] && n>0 && PolynomialQ[v,x] && Exponent[v,x]<=2 && 
  PolynomialQ[w,x] && Exponent[w,x]<=2

