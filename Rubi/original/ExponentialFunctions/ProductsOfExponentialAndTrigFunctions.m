(* ::Package:: *)

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sin[c_.+d_.*x_],x_Symbol] :=
(Print["Int(1th)@ProductsOfExponentialAndTrigFunctions.m"];
  b*p*Log[f]*(f^(a+b*x))^p*Sin[c+d*x]/(d^2+b^2*p^2*Log[f]^2) - 
  d*(f^(a+b*x))^p*Cos[c+d*x]/(d^2+b^2*p^2*Log[f]^2)) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2+b^2*p^2*Log[f]^2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Cos[c_.+d_.*x_],x_Symbol] :=
(Print["Int(2th)@ProductsOfExponentialAndTrigFunctions.m"];
  b*p*Log[f]*(f^(a+b*x))^p*Cos[c+d*x]/(d^2+b^2*p^2*Log[f]^2) + 
  d*(f^(a+b*x))^p*Sin[c+d*x]/(d^2+b^2*p^2*Log[f]^2)) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2+b^2*p^2*Log[f]^2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sin[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(3th)@ProductsOfExponentialAndTrigFunctions.m"];
  b*p*Log[f]*(f^(a+b*x))^p*Sin[c+d*x]^n/(d^2*n^2+b^2*p^2*Log[f]^2) - 
  d*n*(f^(a+b*x))^p*Cos[c+d*x]*Sin[c+d*x]^(n-1)/(d^2*n^2+b^2*p^2*Log[f]^2) + 
  Dist[(n*(n-1)*d^2)/(d^2*n^2+b^2*p^2*Log[f]^2),Int[(f^(a+b*x))^p*Sin[c+d*x]^(n-2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*n^2+b^2*p^2*Log[f]^2] && RationalQ[n] && n>1

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Cos[c_.+d_.*x_]^m_,x_Symbol] :=
(Print["Int(4th)@ProductsOfExponentialAndTrigFunctions.m"];
  b*p*Log[f]*(f^(a+b*x))^p*Cos[c+d*x]^m/(d^2*m^2+b^2*p^2*Log[f]^2) + 
  d*m*(f^(a+b*x))^p*Sin[c+d*x]*Cos[c+d*x]^(m-1)/(d^2*m^2+b^2*p^2*Log[f]^2) + 
  Dist[(m*(m-1)*d^2)/(d^2*m^2+b^2*p^2*Log[f]^2),Int[(f^(a+b*x))^p*Cos[c+d*x]^(m-2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*m^2+b^2*p^2*Log[f]^2] && RationalQ[m] && m>1

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sin[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(5th)@ProductsOfExponentialAndTrigFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Sin[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) + 
  (f^(a+b*x))^p*Cos[c+d*x]*Sin[c+d*x]^(n+1)/(d*(n+1))) /;
FreeQ[{a,b,c,d,f,n,p},x] && ZeroQ[d^2*(n+2)^2+b^2*p^2*Log[f]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Cos[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(6th)@ProductsOfExponentialAndTrigFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Cos[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) - 
  (f^(a+b*x))^p*Sin[c+d*x]*Cos[c+d*x]^(n+1)/(d*(n+1))) /;
FreeQ[{a,b,c,d,f,n,p},x] && ZeroQ[d^2*(n+2)^2+b^2*p^2*Log[f]^2] && NonzeroQ[n+1] && NonzeroQ[n+2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sin[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(7th)@ProductsOfExponentialAndTrigFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Sin[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) + 
  (f^(a+b*x))^p*Cos[c+d*x]*Sin[c+d*x]^(n+1)/(d*(n+1)) + 
  Dist[(d^2*(n+2)^2+b^2*p^2*Log[f]^2)/(d^2*(n+1)*(n+2)),Int[(f^(a+b*x))^p*Sin[c+d*x]^(n+2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*(n+2)^2+b^2*p^2*Log[f]^2] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Cos[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(8th)@ProductsOfExponentialAndTrigFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Cos[c+d*x]^(n+2)/(d^2*(n+1)*(n+2)) - 
  (f^(a+b*x))^p*Sin[c+d*x]*Cos[c+d*x]^(n+1)/(d*(n+1)) + 
  Dist[(d^2*(n+2)^2+b^2*p^2*Log[f]^2)/(d^2*(n+1)*(n+2)),Int[(f^(a+b*x))^p*Cos[c+d*x]^(n+2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[d^2*(n+2)^2+b^2*p^2*Log[f]^2] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sec[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(9th)@ProductsOfExponentialAndTrigFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Sec[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) + 
  (f^(a+b*x))^p*Sec[c+d*x]^(n-1)*Sin[c+d*x]/(d*(n-1))) /;
FreeQ[{a,b,c,d,f,p,n},x] && ZeroQ[b^2*p^2*Log[f]^2+d^2*(n-2)^2] && NonzeroQ[n-1] && NonzeroQ[n-2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Csc[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(10th)@ProductsOfExponentialAndTrigFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Csc[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) + 
  (f^(a+b*x))^p*Csc[c+d*x]^(n-1)*Cos[c+d*x]/(d*(n-1))) /;
FreeQ[{a,b,c,d,f,p,n},x] && ZeroQ[b^2*p^2*Log[f]^2+d^2*(n-2)^2] && NonzeroQ[n-1] && NonzeroQ[n-2]

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Sec[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(11th)@ProductsOfExponentialAndTrigFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Sec[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) + 
  (f^(a+b*x))^p*Sec[c+d*x]^(n-1)*Sin[c+d*x]/(d*(n-1)) + 
  Dist[(b^2*p^2*Log[f]^2+d^2*(n-2)^2)/(d^2*(n-1)*(n-2)),Int[(f^(a+b*x))^p*Sec[c+d*x]^(n-2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[b^2*p^2*Log[f]^2+d^2*(n-2)^2] && RationalQ[n] && n>1 && n!=2

(* ::Code:: *)
Int[(f_^(a_.+b_.*x_))^p_.*Csc[c_.+d_.*x_]^n_,x_Symbol] :=
(Print["Int(12th)@ProductsOfExponentialAndTrigFunctions.m"];
  -b*p*Log[f]*(f^(a+b*x))^p*Csc[c+d*x]^(n-2)/(d^2*(n-1)*(n-2)) - 
  (f^(a+b*x))^p*Csc[c+d*x]^(n-1)*Cos[c+d*x]/(d*(n-1)) + 
  Dist[(b^2*p^2*Log[f]^2+d^2*(n-2)^2)/(d^2*(n-1)*(n-2)),Int[(f^(a+b*x))^p*Csc[c+d*x]^(n-2),x]]) /;
FreeQ[{a,b,c,d,f,p},x] && NonzeroQ[b^2*p^2*Log[f]^2+d^2*(n-2)^2] && RationalQ[n] && n>1 && n!=2

(* ::Code:: *)
Int[x_^m_.*(f_^(a_.+b_.*x_))^p_.*Sin[c_.+d_.*x_]^n_.,x_Symbol] :=
(Print["Int(13th)@ProductsOfExponentialAndTrigFunctions.m"];
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(f^(a+b*x))^p*Sin[c+d*x]^n,x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]]) /;
FreeQ[{a,b,c,d,f,p},x] && RationalQ[m] && m>0 && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_.*(f_^(a_.+b_.*x_))^p_.*Cos[c_.+d_.*x_]^n_.,x_Symbol] :=
(Print["Int(14th)@ProductsOfExponentialAndTrigFunctions.m"];
  Module[{u=Block[{ShowSteps=False,StepCounter=Null}, Int[(f^(a+b*x))^p*Cos[c+d*x]^n,x]]},
  x^m*u - Dist[m,Int[x^(m-1)*u,x]]]) /;
FreeQ[{a,b,c,d,f,p},x] && RationalQ[m] && m>0 && IntegerQ[n] && n>0

(* ::Code:: *)
Int[f_^v_*Sin[w_],x_Symbol] :=
(Print["Int(15th)@ProductsOfExponentialAndTrigFunctions.m"];
  Dist[I/2,Int[f^v/E^(I*w),x]] - 
  Dist[I/2,Int[f^v*E^(I*w),x]]) /;
FreeQ[f,x] && PolynomialQ[v,x] && Exponent[v,x]<=2 && PolynomialQ[w,x] && Exponent[w,x]<=2

(* ::Code:: *)
Int[f_^v_*Cos[w_],x_Symbol] :=
(Print["Int(16th)@ProductsOfExponentialAndTrigFunctions.m"];
  Dist[1/2,Int[f^v*E^(I*w),x]] + 
  Dist[1/2,Int[f^v/E^(I*w),x]]) /;
FreeQ[f,x] && PolynomialQ[v,x] && Exponent[v,x]<=2 && PolynomialQ[w,x] && Exponent[w,x]<=2

(* ::Code:: *)
Int[f_^v_*Sin[w_]^n_,x_Symbol] :=
(Print["Int(17th)@ProductsOfExponentialAndTrigFunctions.m"];
  Dist[(I/2)^n,Int[f^v*(1/E^(I*w)-E^(I*w))^n,x]]) /;
FreeQ[f,x] && IntegerQ[n] && n>0 && PolynomialQ[v,x] && Exponent[v,x]<=2 && 
  PolynomialQ[w,x] && Exponent[w,x]<=2

(* ::Code:: *)
Int[f_^v_*Cos[w_]^n_,x_Symbol] :=
(Print["Int(18th)@ProductsOfExponentialAndTrigFunctions.m"];
  Dist[1/2^n,Int[f^v*(E^(I*w)+1/E^(I*w))^n,x]]) /;
FreeQ[f,x] && IntegerQ[n] && n>0 && PolynomialQ[v,x] && Exponent[v,x]<=2 && 
  PolynomialQ[w,x] && Exponent[w,x]<=2

