(* ::Package:: *)

(*\:4e0e\:6d4b\:8bd5\:7528\:4f8b\:76f8\:6bd4\:540e,Rubi\:4e2d\:672a\:5b9a\:4e49\:7684\:51fd\:6570\:7c7b\:578b*)
(*Algebraic Function Integration*)
Int[Sqrt[(a+b x^n)/x^2],x]
Int[1/Sqrt[(a+x) (b+x)],x]
Int[(Sqrt[1-x]+Sqrt[1+x])^2/x,x]
Simplify[Int[x/(x+Sqrt[x^6]),x]]
Int[1/(x (a+b x)^(1/3)),x]
Int[x^(n/2)/Sqrt[1+x^5],x](*\:90e8\:5206n\:7684\:503c\:65e0\:7ed3\:679c\:ff0c\:5982n=13*)
Int[1/(x+Sqrt[-2+3 x-x^2]),x]

(*Error Function Integration*)
Int[x^m Erf[b x]^2,x]
Int[x^m Erf[a+b x]^2,x]
Int[x^m FresnelS[b x]^2,x]

(*Exponential Function Integration*)
Int[x^m E^(a+b x)^n,x](*\:6709\:5b9a\:4e49\:ff0c\:4f46\:53ea\:80fd\:8ba1\:7b97\:51fa\:8868\:8fbe\:5f0f\:4e2d\:7684\:90e8\:5206\:7ed3\:679c*)
Int[8^x/(a+b 4^x),x]
Int[4^x/(a+b 2^x),x]
Int[E^(a+b x^n) E^(c+d x^n),x]

(*Hyperbolic Function Integration*)
Int[x^m Tanh[a+b x],x](*\:5f53m=1\:65f6\:ff0c\:53ef\:4ee5\:83b7\:5f97\:7ed3\:679c\:ff0c\:5176\:4ed6\:60c5\:51b5\:4e0b\:53ea\:80fd\:8ba1\:7b97\:51fa\:90e8\:5206\:7ed3\:679c*)
Int[x^m/(a+b Sinh[x]),x]
Int[Sec[a+b x]^4 Tan[a+b x]^n,x]
Int[Sqrt[a+b Tanh[x]],x](*\:4ec5\:5f53a==b==1\:65f6\:624d\:80fd\:8ba1\:7b97\:51fa\:7ed3\:679c*)
Int[Sqrt[a+b Coth[x]],x](*\:4ec5\:5f53a==b==1\:65f6\:624d\:80fd\:8ba1\:7b97\:51fa\:7ed3\:679c*)
Int[Sech[x]^2/Sqrt[a-b Tanh[x]^2],x]
Int[Tanh[x]/Sqrt[a+b Tanh[x]^4],x]
Int[Sqrt[Sinh[a+b x]/Cosh[a+b x]],x](*\:4f46\:80fd\:8ba1\:7b97\:51fa Sqrt[Sinh[a+b x]]/Sqrt[Cosh[a+b x]] \:7684\:7ed3\:679c*)

(*Integral Function Integration*)
Int[x^m ExpIntegralEi[a+b x]^2,x]
Int[x^m SinIntegral[a+b x]^2,x]
Int[x^m Cos[b x] SinIntegral[b x],x]
Int[CosIntegral[a+b x] Sin[c+d x],x]

(*Inverse Hyperbolic Function Integration*)
Int[ArcTanh[x]/(a+b x), x]
Int[ArcTanh[x]/(a+b x+c x^2), x]
Int[ArcTanh[a x^n]/x, x]
Int[ArcTanh[a Tanh[x]], x]
Int[ArcSinh[E^(a+b x)], x]

(*Inverse Trig Function Integration*)
Int[ArcSec[a+b x], x](*\:4ec5\:80fd\:8ba1\:7b97\:51fa\:90e8\:5206\:7ed3\:679c,\:9884\:6d4b\:5e94\:8be5\:662f 1/((a+b x) Sqrt[1-1/(a+b x)^2]) \:8fd9\:90e8\:5206\:6ca1\:6709\:79ef\:51fa\:6765*)
Int[ArcSec[a x^n]/x, x](*\:4ec5\:80fd\:8ba1\:7b97\:51fa\:90e8\:5206\:7ed3\:679c*)
Int[ArcTan[x]/(a+b x^2)^(m/2),x](*\:4ec5\:80fd\:8ba1\:7b97\:51fa\:90e8\:5206\:7ed3\:679c*)

(*Logarithm Function Integration*)
Int[Log[a+b x^m]/x, x](*\:5f53a!=1\:65f6\:ff0c\:8ba1\:7b97\:7ed3\:679c\:4e0d\:6b63\:786e*)
Int[Log[a+b x^2]^2/x^3, x]
Int[Log[(c x)/(a+b x)]^3, x]
Int[Log[(a+b x)^2/x^2]^3, x]

(*Rational Function Integration*)
Int[x^p (a x^n+b x^(m n+n+p+1))^m, x](*\:4ec5\:5f53\:5404\:7cfb\:6570\:4e3a\:5177\:4f53\:6570\:5b57\:65f6\:ff0c\:624d\:80fd\:8ba1\:7b97\:51fa\:7ed3\:679c*)
Int[(a+b x)^(n-1) (c+d (a+b x)^n)^m, x]

(*Special Function Integration*)
Int[x^m Gamma[n,a+b x],x]
Int[x^m PolyLog[n,c E^(a+b x)],x]
Int[(Log[x]^m PolyLog[n,a x])/x,x]
Int[x^m ProductLog[a+b x],x]
Int[x^m ProductLog[a+b x]^2]
Int[x^m ProductLog[a x^2],x]
Int[x^m ProductLog[a/x],x]
Int[ProductLog[a/x^(1/(n-1))]^n,x]
Int[ProductLog[a x^n]^p/x^(n(p-1)+1),x]

(*Trig Function Integration*)
Int[1/(1+Sec[a+b x]),x]
Int[Sin[x] Tan[n x],x](*\:4ec5\:5f53n=1\:65f6\:80fd\:8ba1\:7b97\:51fa\:7ed3\:679c*)
Int[Sqrt[Sec[a+b x]^2],x]
Int[Sqrt[Sec[x]^2],x]
Int[Sqrt[Csc[x]^2],x]
Int[Sqrt[1+Sec[x]],x]
Int[Sqrt[1+Csc[x]],x]
Int[Sqrt[c*Cos[x-d]],x]
Int[Sin[x]/Sqrt[a+b Sin[x]^2],x]
Int[Cot[x]/Sqrt[a+b Tan[x]^2+c Tan[x]^4],x]
