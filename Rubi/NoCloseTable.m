(* ::Package:: *)

(*\:67e5\:8868\:83b7\:77e5\:4e0d\:53ef\:79ef\:51fd\:6570*)
(*Stage I//IntTable.m*)
(*Shao Qiming*)
NoCloseList=
{
  A[E^(x_^2),x_]:="NoClose",
  A[E^(-x_^2),x_]:="NoClose",
  A[E^x_/x_,x_]:="NoClose",
  A[1/Log[x_],x_]:="NoClose",
  A[Sin[x_]/x_,x_]:="NoClose",
  A[Cos[x_]/x_,x_]:="NoClose",
  A[Tan[x_]/x_,x_]:="NoClose",
  A[Cot[x_]/x_,x_]:="NoClose",
  A[Sec[x_]/x_,x_]:="NoClose",  
  A[Csc[x_]/x_,x_]:="NoClose",
  A[Sin[x_^2],x_]:="NoClose",
  A[Cos[x_^2],x_]:="NoClose",
  A[Tan[x_^2],x_]:="NoClose",  
  A[Cot[x_^2],x_]:="NoClose",
  A[Sec[x_^2],x_]:="NoClose",
  A[Csc[x_^2],x_]:="NoClose",
  A[Sinh[x_^2],x_]:="NoClose",
  A[Cosh[x_^2],x_]:="NoClose",
  A[Tanh[x_^2],x_]:="NoClose",
  A[x_/Sin[x_],x_]:="NoClose",
  A[x_/Cos[x_],x_]:="NoClose",
  A[x_/Tan[x_],x_]:="NoClose",
  A[x_/Cot[x_],x_]:="NoClose",
  A[x_/ArcSin[x_],x_]:="NoClose",  
  A[x_/ArcCos[x_],x_]:="NoClose",  
  A[x_/ArcTan[x_],x_]:="NoClose",  
  A[x_/ArcCot[x_],x_]:="NoClose",    
  A[x_/ArcSec[x_],x_]:="NoClose",  
  A[x_/ArcCsc[x_],x_]:="NoClose" 

};


NoClose[f_,x_] := Module[
{r = A[f,x]},
If[Head[r] === A, Return["NotMatch"], Return["NoClose"]]
]


NoClose[E^(x^2),x]
NoClose[x/ArcCsc[x],x]
NoClose[Sec[x^2],x]
NoClose[x E^x,x]



