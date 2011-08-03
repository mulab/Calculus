(* ::Package:: *)

Int[ArcSec[a_+b_ x_], x_] := ((a+b x) ArcSec[a+b x])/b-ArcTanh[Sqrt[1-1/(a+b x)^2]]/b/;FreeQ[{a,b},x]&&NonzeroQ[b]


Int[ArcSec[a_ x_^n_]/x_, x_] := (I ArcSec[a x^n]^2)/(2 n)-(ArcSec[a x^n] Log[1-1/((I x^-n)/a+Sqrt[1-x^(-2 n)/a^2])^2])/n+(I PolyLog[2,1/((I x^-n)/a+Sqrt[1-x^(-2 n)/a^2])^2])/(2 n)/;FreeQ[{a,n},x]&&NonzeroQ[n]&&NonzeroQ[a]


(*ArcTan[x]/(a+b x^2)^(m/2)*)
