(* ::Package:: *)

(*\:79ef\:5206\:8868\:529f\:80fd\:ff0c\:6ce8\:610f\:548cDDM\:51d1\:5fae\:5206\:65b9\:6cd5\:7684\:5206\:79bb\:ff0c\:79ef\:5206\:8868\:4e2d\:4e0d\:5e94\:8be5\:5305\:542b\:8f6c\:6362\:89c4\:5219\:ff0c
\:5e94\:8be5\:662f\:79ef\:51fa\:6765\:7684\:7ed3\:679c\:ff0c\:4e14\:53ea\:8fdb\:884c\:4e00\:6b21\:66ff\:6362\:3002\:8be5\:8868\:8fd8\:53ef\:4ee5\:6269\:5927*)
(*Shao Qiming , shaoqiming8@gmail.com/15210589502*)
(*\:6ce8\:610fax+b\:5e94\:8be5\:5206\:6210\:56db\:6761\:89c4\:5219\:6765\:5199\:ff0c\:5185\:6838\:6682\:65f6\:4e0d\:63d0\:4f9boptional\:51fd\:6570*)
(**)
IntegrateList=
{
(*  A[a_ f_, x_] /; FreeQ[a, x] :>  a A[f, x] ,*)
  A[a_, x_] /; FreeQ[a, x] :>  a x ,
  A[x_, x_]  :>  x^2/2 ,
(*  A[f_ + g_, x_]  :>  A[f, x] + A[g, x],*)
  A[x_^n_ Sqrt[a_ x_ + b_], x_] /; FreeQ[n, x] && FreeQ[a, x] && FreeQ[b, x] :>  
		(2 x^n)/((2 n + 3) a) (Sqrt[(a x + b)])^3 - (2 n b)/((2 n + 3) a) A[x^(n - 1) Sqrt[a x + b], x] ,
(*  A[f_[a_ x_ + b_], x_] /; FreeQ[{a, b}, x] :>  A[f[a x + b],a x + b] / a ,*)
(*  A[Sqrt[x_^n_],x_] /;x>0 :> x^(n/2+1)/(n/2+1),
  A[a_ Sqrt[x_^n_],x_] /;FreeQ[a,x]:> x^(n/2+1)/(n/2+1),*)
  A[1,x_] :> x,
  A[1/x_,x_] :> Log[x],
  A[x_^n_, x_] /; FreeQ[{n}, x] :>  x^(1 + n)/(1 + n) ,
  A[E^x_, x_]  :>  E^x,
  A[a_^x_, x_] /; FreeQ[{a}, x] :>  a^x/Log[a] ,
  A[1/(1 + x_^2), x_]  :>  ArcTan[x],
  A[1/(1 - x_^2), x_]  :>  1/2 Log[-1 - x] - 1/2 Log[-1 + x],
  A[1/(2 Sqrt[x_]),x_] :> Sqrt[x],
  A[1/Sqrt[1 - x_^2], x_]  :>  ArcSin[x],
  A[1/Sqrt[1 + x_^2], x_]  :>  ArcSinh[x],
  A[1/Sqrt[-1 + x_^2], x_]  :>  Log[2 (x + Sqrt[-1 + x^2])],
  A[1/(1 - x_^2), x_]  :>  1/2 Log[-1 - x] - 1/2 Log[-1 + x],
  A[Sqrt[x_ + Sqrt[x_]], x_]  :>  1/12 Sqrt[Sqrt[x] + x] (-3 + 2 Sqrt[x] + 8 x) + 1/8 Log[1 + 2 Sqrt[x] + 2 Sqrt[Sqrt[x] + x]],

  (*Integration with Tirg={Sin,Cos,Tan,Cot,Sec,Csc,Sinh,Coth,Tanh,ArcSin,ArcCos,ArcTan,ArcCot,ArcSec,ArcCsc}*)

  A[Sin[x_], x_]  :>  -Cos[x],
  A[Cos[x_], x_]  :>  Sin[x],
  A[Csc[x_]^2, x_]  :>  -Cot[x],
  A[Sec[x_]^2, x_]  :>  Tan[x],
  A[Sec[x_] Tan[x_], x_]  :>  Sec[x],
  A[Cot[x_] Csc[x_], x_]  :>  -Csc[x],
  A[Tan[x_], x_]  :>  -Log[Cos[x]],
  A[Cot[x_], x_]  :>  Log[Sin[x]],
  A[Csc[x_], x_]  :>  -Log[2 Cos[x/2]] + Log[2 Sin[x/2]],
  A[Sec[x_], x_]  :>  -Log[Cos[x/2] - Sin[x/2]] + Log[Cos[x/2] + Sin[x/2]],
  A[Sinh[x_], x_]  :>  Cosh[x],
  A[Cosh[x_], x_]  :>  Sinh[x],
  A[Csch[x_]^2, x_]  :>  -Coth[x],
  A[Sech[x_]^2, x_]  :>  Tanh[x],
  A[Tanh[x_], x_]  :>  Log[Cosh[x]],
  A[Coth[x_], x_]  :>  Log[Sinh[x]],
  A[Csch[x_], x_]  :>  -Log[2 Cosh[x/2]] + Log[2 Sinh[x/2]],  
  A[Sin[a_ x_],x_] /;FreeQ[{a},x]:> -(Cos[a x]/a),
  A[Cos[a_ x_],x_] /;FreeQ[{a},x] :> Sin[a x]/a,
  A[Sin[a_ x_]^2,x_]/;FreeQ[{a},x] :> x/2 - Sin[2 a x]/(4 a),
  A[Cos[a_ x_]^2,x_] /;FreeQ[{a},x]:> x/2 + Sin[2 a x]/(4 a),
  A[1/(1+Sin[a_ x_]),x_] /;FreeQ[{a},x]:> -1/a*Tan[Pi/4 -a x/2],
  A[1/(1+Cos[a_ x_]),x_]/;FreeQ[{a},x] :> 1/a*Tan[a x/2],
  A[1/(b_+c_Sin[a_ x_]),x_] /;FreeQ[{a},x]:> (2 ArcTan[(1 + b Tan[(c x)/2])/Sqrt[-1 + b^2]])/(Sqrt[-1 + b^2] c),
  A[1/(b_+c_Cos[a_ x_]),x_]/;FreeQ[{a},x] :> (-2 ArcTanh[((-1 + b) Tan[(c x)/2])/Sqrt[1 - b^2]])/(Sqrt[1 - b^2] c),
  A[Tan[a_ x_],x_] /;FreeQ[{a},x]:> -(Log[Cos[a x]]/a),
  A[Sec[a_ x_],x_]/;FreeQ[{a},x] :> -(Log[Cos[(a x)/2] - Sin[(a x)/2]]/a) + Log[Cos[(a x)/2] + Sin[(a x)/2]]/a,
  A[Sinh[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> (Cosh[b] Cosh[a x])/a + (Sinh[b] Sinh[a x])/a,
  A[Coth[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> Log[Sinh[b + a x]]/a,
  A[Tanh[a_ x_ +b_],x_] /;FreeQ[{a,b},x]:> Log[Cosh[b + a x]]/a,
  A[1/Sin[a_ x_ +b_],x_] /;FreeQ[{a,b},x]:> -(Log[2 Cos[b/2 + (a x)/2]]/a) + Log[2 Sin[b/2 + (a x)/2]]/a,
  A[1/Cos[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> -(Log[Cos[b/2 + (a x)/2] - Sin[b/2 + (a x)/2]]/a) + Log[Cos[b/2 + (a x)/2] + Sin[b/2 + (a x)/2]]/a,
  A[1/Tan[a_ x_ +b_],x_] /;FreeQ[{a,b},x]:> Log[Sin[b + a x]]/a,
  A[1/Cot[a_ x_ +b_],x_] /;FreeQ[{a,b},x]:> -(Log[Cos[b + a x]]/a),
  A[1/Sec[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> (Cos[a x] Sin[b])/a + (Cos[b] Sin[a x])/a,
  A[1/Sinh[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> -(Log[2 Cosh[b/2 + (a x)/2]]/a) + Log[2 Sinh[b/2 + (a x)/2]]/a,
  A[1/Coth[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> Log[Cosh[b + a x]]/a,
  A[1/Tanh[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> Log[Sinh[b + a x]]/a,
  A[1/(Sin[a_ x_ + b_]^2), x_]/;FreeQ[{a,b},x] :> -(Cot[b + a x]/a),
  A[1/(Cos[a_ x_ + b_]^2), x_]/;FreeQ[{a,b},x] :> Tan[b + a x]/a,
  A[1/(Tan[a_ x_ + b_]^2), x_] /;FreeQ[{a,b},x]:> -x - Cot[b + a x]/a,
  A[1/(Cot[a_ x_ + b_]^2), x_]/;FreeQ[{a,b},x] :> -x + Tan[b + a x]/a,
  A[1/(Sec[a_ x_ + b_]^2), x_] /;FreeQ[{a,b},x]:> (2 (b + a x) + Sin[2 (b + a x)])/(4 a),
  A[1/(Csc[a_ x_ + b_]^2), x_]/;FreeQ[{a,b},x] :> -(-2 (b + a x) + Sin[2 (b + a x)])/(4 a),
  A[Sin[a_ x_ + b_], x_]/; FreeQ[{a,b}, x] :> -1/a Cos[a x + b],
  A[Cos[a_ x_ + b_], x_]/; FreeQ[{a,b},x] :> 1/a Sin[a x  + b],
  A[Tan[a_ x_ + b_],x_] /;FreeQ[{a,b},x]:> -Log[Cos[a x  + b ]]/a,
  A[Cot[a_ x_ + b_],x_]/;FreeQ[{a,b},x] :> -Log[Sin[a x  + b ]]/a,
  A[Sec[a_ x_ +b_],x_] /;FreeQ[{a,b},x]:> (Log[Sin[(a x )/2 + b/2]+Cos[(a x )/2 + b/2]]-Log[Cos[(a x )/2 + b/2]-Sin[(a x )/2 + b/2]])/a,
  A[ArcSin[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> (Sqrt[- a^2 x^2 -a b x - b^2 + 1]+(a x + b)ArcSin[a x + b])/a,
  A[ArcCos[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> x ArcCos[a x + b] - (Sqrt[-a^2 x^2 - 2 a b x - b^2 + 1] + b ArcSin[a x + b])/a,
  A[ArcTan[a_ x_ +b_],x_] /;FreeQ[{a,b},x]:> -(Log[a^2x^2 + 2a b x + b^2 + 1] - 2(a x + b)ArcTan[a x + b])/(2a),
  A[ArcCot[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> (Log[a^2x^2 + 2a b x + b^2 + 1] - 2b ArcTan[a x + b])/(2a)+x ArcCot[a x + b],
  A[ArcSec[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> x ArcSec[b + a x] - ((b + a x) Sqrt[(-1 + b^2 + 2 a b x + a^2 x^2)/(b + a x)^2] (b ArcTan[1/Sqrt[-1 + b^2 + 2 a b x + a^2 x^2]] + Log[2 (b + a x + Sqrt[-1 + b^2 + 2 a b x + a^2 x^2])]))/(a Sqrt[-1 + b^2 + 2 a b x + a^2 x^2]),
  A[ArcCsc[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> x ArcCsc[b + a x] + ((b + a x) Sqrt[(-1 + b^2 + 2 a b x + a^2 x^2)/(b + a x)^2] (b ArcTan[1/Sqrt[-1 + b^2 + 2 a b x + a^2 x^2]] + Log[2 (b + a x + Sqrt[-1 + b^2 + 2 a b x + a^2 x^2])]))/(a Sqrt[-1 + b^2 + 2 a b x + a^2 x^2]),

  (*Integration with Tirg={Sin,Cos,Tan,Cot,Sec,Csc,Sinh,Coth,Tanh,ArcSin,ArcCos,ArcTan,ArcCot,ArcSec,ArcCsc}*)
  
  
  (*Integration with parameter*)

  A[Log[a_ x_ +b_],x_]/;FreeQ[{a,b},x] :> -x + (b Log[b + a x])/a + x Log[b + a x],
  A[E^(a_ x_ +b_),x_]/;FreeQ[{a,b},x] :> E^(b + a x)/a,
  A[c_^(a_ x_ +b_),x_]/;FreeQ[{a,b,c},x]:> c^(b + a x)/(a Log[c]),
  A[1/(a_x +b_),x_] /;FreeQ[{a,b},x]:> Log[b + a x]/a,
  A[Sqrt[b_ + a_ x_], x_]  /;FreeQ[{a, b}, x]:> (2 (b + a x)^(3/2))/(3 a),
  A[x_ Sqrt[b_ + a_ x_],x_]/;FreeQ[{a, b}, x] :> (2 Sqrt[b + a x] (-2 b^2 + a b x + 3 a^2 x^2))/(15 a^2) ,
  A[1/(x_^2 +a_^2),x_] /;FreeQ[{a},x] && a!=0:> ArcTan[x/a]/a,
  A[1/(x_^2 -a_^2),x_] /;FreeQ[{a},x] && a!=0:> -(ArcTanh[x/a]/a),
  A[1/(a_^3 +x_^3),x_] /;FreeQ[{a},x]:> (2 Sqrt[3] ArcTan[(-a + 2 x)/(Sqrt[3] a)] + 2 Log[a + x] - Log[a^2 - a x + x^2])/(6 a^2),
  A[1/(a_^3 -x_^3),x_] /;FreeQ[{a},x]:> (2 Sqrt[3] ArcTan[(a + 2 x)/(Sqrt[3] a)] - 2 Log[-a + x] + Log[a^2 + a x + x^2])/(6 a^2),
  A[x_/(a_^3 +x_^3),x_]/;FreeQ[{a},x] :> (2 Sqrt[3] ArcTan[(-a + 2 x)/(Sqrt[3] a)] - 2 Log[a + x] + Log[a^2 - a x + x^2])/(6 a),
  A[x_/(a_^3 -x_^3),x_]/;FreeQ[{a},x]:> (-2 Sqrt[3] ArcTan[(a + 2 x)/(Sqrt[3] a)] - 2 Log[-a + x] + Log[a^2 + a x + x^2])/(6 a),
  A[x_^2/(a_^3 +x_^3),x_] /;FreeQ[{a},x]:> Log[a^3 + x^3]/3,
  A[x_^2/(a_^3 -x_^3),x_] /;FreeQ[{a},x]:> -Log[a^3 - x^3]/3,
  A[1/(a_^4 +x_^4),x_]/;FreeQ[{a},x] :> (-2 ArcTan[1 - (Sqrt[2] x)/a] + 2 ArcTan[1 + (Sqrt[2] x)/a] - Log[a^2 - Sqrt[2] a x + x^2] + Log[a^2 + Sqrt[2] a x + x^2])/(4 Sqrt[2] a^3),
  A[1/(a_^4 -x_^4),x_]/;FreeQ[{a},x] :> ArcTan[x/a]/(2 a^3) - Log[-a + x]/(4 a^3) + Log[a + x]/(4 a^3),
  A[x_/(a_^4 +x_^4),x_]/;FreeQ[{a},x] :> ArcTan[x^2/a^2]/(2 a^2),
  A[x_/(a_^4 -x_^4),x_] /;FreeQ[{a},x]:> ArcTanh[x^2/a^2]/(2 a^2),
  A[x_^2/(a_^4 +x_^4),x_] /;FreeQ[{a},x]:> (-2 ArcTan[1 - (Sqrt[2] x)/a] + 2 ArcTan[1 + (Sqrt[2] x)/a] + Log[a^2 - Sqrt[2] a x + x^2] - Log[a^2 + Sqrt[2] a x + x^2])/(4 Sqrt[2] a),
  A[x_^2/(a_^4 -x_^4),x_]/;FreeQ[{a},x] :> -ArcTan[x/a]/(2 a) - Log[-a + x]/(4 a) + Log[a + x]/(4 a),
  A[x_^3/(a_^4 -x_^4),x_]/;FreeQ[{a},x] :> Log[a^4 + x^4]/4,
  A[x_^3/(a_^4 -x_^4),x_]/;FreeQ[{a},x] :> -Log[a^4 - x^4]/4,
  
  A[x_ (a_ x_ +b_)^n_,x_] /;FreeQ[{a,b,n},x]&& n!=-1 && n!=-2:> ((b + a x)^(1 + n) (-b + a (1 + n) x))/(a^2 (1 + n) (2 + n)),
  A[x_/(a_ x_ +b_),x_]/;FreeQ[{a,b},x] :> x/a - (b Log[b + a x])/a^2,
  A[x_/(a_ x_ +b_)^2,x_]/;FreeQ[{a,b},x] :> (b/(b + a x) + Log[b + a x])/a^2,
  A[1/(x_ Sqrt[a_ x_ +b_]),x_] /;FreeQ[{a,b},x]:> (-2 ArcTanh[Sqrt[b + a x]/Sqrt[b]])/Sqrt[b],
  A[Sqrt[a_ x_ +b_]/x_,x_]/;FreeQ[{a,b},x] :> 2 Sqrt[b + a x] - 2 Sqrt[b] ArcTanh[Sqrt[b + a x]/Sqrt[b]],
  A[Sqrt[a_ x_ +b_]/x_^2,x_]/;FreeQ[{a,b},x] :> -(Sqrt[b + a x]/x) - (a ArcTanh[Sqrt[b + a x]/Sqrt[b]])/Sqrt[b],
  A[1/(x_^2 Sqrt[a_ x_ +b_]),x_]/;FreeQ[{a,b},x] :> -(Sqrt[b + a x]/(b x)) + (a ArcTanh[Sqrt[b + a x]/Sqrt[b]])/b^(3/2),
  A[1/(a_^2 +x_^2)^2,x_]/;FreeQ[{a},x] :> ((a x)/(a^2 + x^2) + ArcTan[x/a])/(2 a^3),
  A[1/(a_^2 -x_^2)^2,x_] /;FreeQ[{a},x]:> ((a x)/(a^2 - x^2) + ArcTanh[x/a])/(2 a^3),
  A[1/Sqrt[x_^2 +a_^2],x_]/;FreeQ[{a},x] :> Log[2 (x + Sqrt[a^2 + x^2])],
  A[1/Sqrt[x_^2 -a_^2],x_]/;FreeQ[{a},x] :> Log[2 (x + Sqrt[-a^2 + x^2])],
  A[Sqrt[a_^2 -x_^2],x_] /;FreeQ[{a},x]:> (x Sqrt[a^2 - x^2] + a^2 ArcTan[x/Sqrt[a^2 - x^2]])/2,
  A[Sqrt[x_^2 +a_^2],x_]/;FreeQ[{a},x] :> (x Sqrt[a^2 + x^2])/2 + (a^2 Log[2 (x + Sqrt[a^2 + x^2])])/2,
  A[Sqrt[x_^2 -a_^2],x_] /;FreeQ[{a},x]:> (x Sqrt[-a^2 + x^2])/2 - (a^2 Log[2 (x + Sqrt[-a^2 + x^2])])/2,
  A[Sqrt[x_^2 + a_],x_] /;FreeQ[{a},x]:> x/2 Sqrt[x^2+a]+a/2 Log[x+Sqrt[x^2+a]],
  A[Sqrt[a_ x_^2 +b_ x_ +c_],x_]/;FreeQ[{a},x]&&FreeQ[{b},x]&&FreeQ[{c},x]:>(2 Sqrt[a] (b+2 a x) Sqrt[c+x (b+a x)]-(b^2-4 a c) Log[b+2 a x+2 Sqrt[a] Sqrt[c+x (b+a x)]])/(8 a^(3/2)),
  A[(x_^2 +a_)^(3/2),x_]/;FreeQ[{a},x] :> Sqrt[a + x^2] ((5 a x)/8 + x^3/4) + (3 a^2 Log[2 (x + Sqrt[a + x^2])])/8,
  A[(x_^2 -a_)^(3/2),x_] /;FreeQ[{a},x]:> Sqrt[-a + x^2] ((-5 a x)/8 + x^3/4) + (3 a^2 Log[2 (x + Sqrt[-a + x^2])])/8,
  A[1/(x_^2 +a_^2)^(3/2),x_]/;FreeQ[{a},x] :> x/(a^2 Sqrt[a^2 + x^2]),
  A[1/(x_^2 -a_^2)^(3/2),x_]/;FreeQ[{a},x] :> -(x/(a^2 Sqrt[-a^2 + x^2])),
  A[1/Sqrt[2 a_ x_ -x_^2],x_]/;FreeQ[{a},x] :> ArcSin[(x-a)/a],
  A[Sqrt[2 a_ x_ -x_^2],x_] /;FreeQ[{a},x]:> (x-a)/2 Sqrt[2 a x-x^2]+a^2/2 ArcSin[(x-a)/a],
  A[x_ Sqrt[2 a_ x_ -x_^2],x_] /;FreeQ[{a},x]:> (x+a) (2 x-3 a) Sqrt[2 a x-x^2]/6+a^3/2 ArcSin[(x-a)/a],
  A[Sqrt[2 a_ x_ -x_^2]/x_,x_]/;FreeQ[{a},x] :> Sqrt[2 a x-x^2]+a ArcSin[(x-a)/a],
  A[Sqrt[2 a_ x_ -x_^2]/x_^2,x_]/;FreeQ[{a},x] :> -2 Sqrt[(2 a-x)/x] -ArcSin[(x-a)/a],
  A[x_/Sqrt[2 a_ x_ -x_^2],x_]/;FreeQ[{a},x] :> a ArcSin[(x-a)/a]-Sqrt[2 a x-x^2],
  A[1/(x_ Sqrt[2 a_ x_ -x_^2]),x_]/;FreeQ[{a},x] :> -1/a Sqrt[(2 a-x)/x],
  A[Sqrt[(a_+x_)/(b_+x_)],x_] /;FreeQ[{a,b},x]:> (Sqrt[(a + x)/(b + x)] (2 Sqrt[a + x] (b + x) + (a - b) Sqrt[b + x] Log[a + b + 2 x + 2 Sqrt[a + x] Sqrt[b + x]]))/(2 Sqrt[a + x]),
  A[Sqrt[(a_-x_)/(b_+x_)],x_] /;FreeQ[{a,b},x]:> (Sqrt[(a - x)/(b + x)] (2 (b + x) - ((a + b) Sqrt[b + x] ArcTan[(a - b - 2 x)/(2 Sqrt[a - x] Sqrt[b + x])])/Sqrt[a - x]))/2,
  A[1/Sqrt[(x_-a_) (b_-x_)],x_] /;FreeQ[{a,b},x]:> -((Sqrt[b - x] Sqrt[-a + x] ArcTan[(a + b - 2 x)/(2 Sqrt[b - x] Sqrt[-a + x])])/Sqrt[(a - x) (-b + x)]),
  A[1/(x_^4+a_^4),x_]/;FreeQ[{a},x] :> (-2 ArcTan[1 - (Sqrt[2] x)/a] + 2 ArcTan[1 + (Sqrt[2] x)/a] - Log[a^2 - Sqrt[2] a x + x^2] + Log[a^2 + Sqrt[2] a x + x^2])/(4 Sqrt[2] a^3),
  A[1/(a_^4-x_^4),x_]/;FreeQ[{a},x] :> ArcTan[x/a]/(2 a^3) - Log[-a + x]/(4 a^3) + Log[a + x]/(4 a^3),
  A[x_^n_ Log[a_ x_],x_]/;FreeQ[{a,n},x] :> (x^(1 + n) (-1 + (1 + n) Log[a x]))/(1 + n)^2,
  A[b_^(a_ x_),x_] /;FreeQ[a,x]:> b^(a x)/(a Log[b]),
  (*Integration with parameter*)

  (*Integration with E*)
  A[E^(a_ x_),x_] /;FreeQ[{a},x] :> E^(a x)/a,
  A[b_^(a_ x_),x_] /;FreeQ[{a,b},x]:> b^(a x)/(a Log[b]),
  A[E^(a_ x_) Sin[b_ x_], x_]/;FreeQ[{a,b},x] :> (E^(a x) (-(b Cos[b x]) + a Sin[b x]))/(a^2 + b^2),
  A[E^(a_ x_) Cos[b_ x_], x_]/;FreeQ[{a,b},x] :> (E^(a x) (a Cos[b x] + b Sin[b x]))/(a^2 + b^2),
  (*Integration with E*)
  (*new*)
  A[1/(x_+a_),x_]/;FreeQ[a,x] :>  Log[x+a],
  A[1/(a_ x_ +b_),x_]/;FreeQ[{a,b},x] :>  Log[a x+b]/a,
  A[x_(E^x_),x_] :> -E^x + x(E^x),
  A[x_(E^(x_+a_)),x_]/;FreeQ[a,x] :> x E^x -E^x+x^2 E^a/2,
  A[x_(E^(a_ x_)),x_]/;FreeQ[a,x] :> x (E^(a x))/a-E^(a x)/a^2,
  A[x_(E^(a_ x_+b_)),x_]/;FreeQ[{a,b},x] :> x (E^(a x+b))/a -E^(a x+ b)/a^2 ,
  A[x_/Sqrt[a_+x_^2],x_]/;FreeQ[a,x] :>  Sqrt[a+x^2] ,
  A[a_ x_/Sqrt[b_ +x_^2],x_]/;FreeQ[{a,b},x] :> a Sqrt[b+x^2],
  A[x_/Sqrt[a_+b_ x_^2],x_]/;FreeQ[{a,b},x]&&b=!=0 :> Sqrt[a+b x^2]/b,
  A[a_ x_/Sqrt[b_+c_ x_^2],x_]/;FreeQ[{a,b,c},x]&&c=!=0 :> a Sqrt[b+c x^2]/c
  (*new*)

};


IntTable[f_,x_]:=Module[
    {},
    ret=A[f,x]//.IntegrateList;
    If[Head[ret]===A,Return["NotFound"],Return[ret]];
	Return["NotFound"]
];


(*IntTable[Sqrt[10 x^3],x]
IntTable[2,x]
IntTable[x,x]
IntTable[Sin[x],x]*)
IntTable[Sqrt[a x^2+b x+c],x]
