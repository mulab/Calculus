(* ::Package:: *)

Int[a_ f_,x_]:= a Int[f,x]/; FreeQ[a,x]


Int[a_,x_] := a x /;FreeQ[a,x]


Int[x_,x_] := x^2/2


Int[f_ + g_,x_] := Int[f,x]+Int[g,x]


Int[x_^n_ Sqrt[a_ x_ + b_] x_] :=  (2 x^n)/((2 n + 3) a) (Sqrt[(a x + b)])^3 - (2 n b)/((2 n + 3) a) Int[x^(n - 1) Sqrt[a x + b] x] /; FreeQ[n, x] && FreeQ[a, x] && FreeQ[b, x] 



Int[f_[a_ x_ + b_] x_] :=  Int[f[a x + b],a x + b] / a /; FreeQ[{a, b} ,x] 


Int[1,x_]:=x


Int[1/x_,x_]:=Log[x]


Int[x_^n_, x_] /; FreeQ[{n}, x] :=  x^(1 + n)/(1 + n)  /; FreeQ[{n} ,x]


Int[E^x_, x_]  :=  E^x


Int[a_^x_, x_]:=  a^x/Log[a]  /; FreeQ[{a} ,x] 


Int[1/(1 + x_^2) ,x_]  :=  ArcTan[x]


Int[1/(1 - x_^2) ,x_]  :=  1/2 Log[-1 - x] - 1/2 Log[-1 + x]


Int[1/(2 Sqrt[x_]),x_] := Sqrt[x]


Int[1/Sqrt[1 - x_^2], x_]  :=  ArcSin[x]


Int[1/Sqrt[1 + x_^2] ,x_]  :=  ArcSinh[x]


Int[1/Sqrt[-1 + x_^2] ,x_]  :=  Log[2 (x + Sqrt[-1 + x^2])]


Int[1/(1 - x_^2) ,x_]  :=  1/2 Log[-1 - x] - 1/2 Log[-1 + x]


Int[Sqrt[x_ + Sqrt[x_]], x_]  :=  1/12 Sqrt[Sqrt[x] + x] (-3 + 2 Sqrt[x] + 8 x) + 1/8 Log[1 + 2 Sqrt[x] + 2 Sqrt[Sqrt[x] + x]]


Int[Sin[x_], x_]  :=  -Cos[x]


Int[Cos[x_], x_]  :=  Sin[x]


Int[Csc[x_]^2, x_]  :=  -Cot[x]


Int[Sec[x_]^2, x_]  :=  Tan[x]


Int[Sec[x_] Tan[x_], x_]  :=  Sec[x]


Int[Cot[x_] Csc[x_], x_]  :=  -Csc[x]


Int[Tan[x_], x_]  :=  -Log[Cos[x]]


Int[Cot[x_], x_]  :=  Log[Sin[x]]


Int[Csc[x_], x_]  :=  -Log[2 Cos[x/2]] + Log[2 Sin[x/2]]


Int[Sec[x_], x_]  :=  -Log[Cos[x/2] - Sin[x/2]] + Log[Cos[x/2] + Sin[x/2]]


Int[Sinh[x_], x_]  :=  Cosh[x]


Int[Cosh[x_], x_]  :=  Sinh[x]


Int[Csch[x_]^2, x_]  :=  -Coth[x]


Int[Sech[x_]^2, x_]  :=  Tanh[x]


Int[Tanh[x_], x_]  :=  Log[Cosh[x]]


Int[Coth[x_], x_]  :=  Log[Sinh[x]]


Int[Csch[x_], x_]  :=  -Log[2 Cosh[x/2]] + Log[2 Sinh[x/2]]


Int[Sin[a_ x_],x_] := -(Cos[a x]/a)/;FreeQ[{a},x]


Int[Cos[a_ x_],x_]:= Sin[a x]/a /;FreeQ[{a},x]


Int[Sin[a_ x_]^2,x_] := x/2 - Sin[2 a x]/(4 a)/;FreeQ[{a},x]


Int[Cos[a_ x_]^2,x_] := x/2 + Sin[2 a x]/(4 a)/;FreeQ[{a},x]


Int[1/(1+Sin[a_ x_]),x_] := -1/a*Tan[Pi/4 -a x/2]/;FreeQ[{a},x]


Int[1/(1+Cos[a_ x_]),x_]:= 1/a*Tan[a x/2]/;FreeQ[{a},x] 


Int[1/(b_+c_Sin[a_ x_]),x_]:= (2 ArcTan[(1 + b Tan[(c x)/2])/Sqrt[-1 + b^2]])/(Sqrt[-1 + b^2] c)/;FreeQ[{a},x]


Int[1/(b_+c_Cos[a_ x_]),x_]:= (-2 ArcTanh[((-1 + b) Tan[(c x)/2])/Sqrt[1 - b^2]])/(Sqrt[1 - b^2] c)/;FreeQ[{a},x] 


Int[Tan[a_ x_],x_] := -(Log[Cos[a x]]/a)/;FreeQ[{a},x]


Int[Sec[a_ x_],x_] := -(Log[Cos[(a x)/2] - Sin[(a x)/2]]/a) + Log[Cos[(a x)/2] + Sin[(a x)/2]]/a/;FreeQ[{a},x]


Int[Sinh[a_ x_ +b_],x_]:= (Cosh[b] Cosh[a x])/a + (Sinh[b] Sinh[a x])/a/;FreeQ[{a,b},x] 


Int[Coth[a_ x_ +b_],x_]:= Log[Sinh[b + a x]]/a/;FreeQ[{a,b},x] 


Int[Tanh[a_ x_ +b_],x_]:= Log[Cosh[b + a x]]/a /;FreeQ[{a,b},x]


Int[1/Sin[a_ x_ +b_],x_] := -(Log[2 Cos[b/2 + (a x)/2]]/a) + Log[2 Sin[b/2 + (a x)/2]]/a/;FreeQ[{a,b},x]


Int[1/Cos[a_ x_ +b_],x_]:= -(Log[Cos[b/2 + (a x)/2] - Sin[b/2 + (a x)/2]]/a) + Log[Cos[b/2 + (a x)/2] + Sin[b/2 + (a x)/2]]/a/;FreeQ[{a,b},x] 


Int[1/Tan[a_ x_ +b_],x_]:= Log[Sin[b + a x]]/a /;FreeQ[{a,b},x]


Int[1/Cot[a_ x_ +b_],x_]:= -(Log[Cos[b + a x]]/a) /;FreeQ[{a,b},x]


Int[1/Sec[a_ x_ +b_],x_]:= (Cos[a x] Sin[b])/a + (Cos[b] Sin[a x])/a /;FreeQ[{a,b},x] 


Int[1/Sinh[a_ x_ +b_],x_]:= -(Log[2 Cosh[b/2 + (a x)/2]]/a) + Log[2 Sinh[b/2 + (a x)/2]]/a /;FreeQ[{a,b},x] 


Int[1/Coth[a_ x_ +b_],x_]:= Log[Cosh[b + a x]]/a /;FreeQ[{a,b},x] 


Int[1/Tanh[a_ x_ +b_],x_]:= Log[Sinh[b + a x]]/a/;FreeQ[{a,b},x] 


Int[1/(Sin[a_ x_ + b_]^2), x_]:= -(Cot[b + a x]/a)/;FreeQ[{a,b},x] 


Int[1/(Cos[a_ x_ + b_]^2), x_]:= Tan[b + a x]/a/;FreeQ[{a,b},x] 


Int[1/(Tan[a_ x_ + b_]^2), x_] := -x - Cot[b + a x]/a /;FreeQ[{a,b},x]


Int[1/(Cot[a_ x_ + b_]^2), x_]:= -x + Tan[b + a x]/a /;FreeQ[{a,b},x] 


Int[1/(Sec[a_ x_ + b_]^2), x_]:= (2 (b + a x) + Sin[2 (b + a x)])/(4 a)/;FreeQ[{a,b},x]


Int[1/(Csc[a_ x_ + b_]^2), x_]:= -(-2 (b + a x) + Sin[2 (b + a x)])/(4 a)/;FreeQ[{a,b},x]


Int[Sin[a_ x_ + b_], x_] := -1/a Cos[a x + b] /; FreeQ[{a,b}, x]


Int[Cos[a_ x_ + b_], x_]:= 1/a Sin[a x  + b] /; FreeQ[{a,b},x] 


Int[Tan[a_ x_ + b_],x_]:= -Log[Cos[a x  + b ]]/a /;FreeQ[{a,b},x]


Int[Cot[a_ x_ + b_],x_]:= -Log[Sin[a x  + b ]]/a /;FreeQ[{a,b},x]


Int[Sec[a_ x_ +b_],x_]:= (Log[Sin[(a x )/2 + b/2]+Cos[(a x )/2 + b/2]]-Log[Cos[(a x )/2 + b/2]-Sin[(a x )/2 + b/2]])/a /;FreeQ[{a,b},x]


Int[ArcSin[a_ x_ +b_],x_]:= (Sqrt[- a^2 x^2 -a b x - b^2 + 1]+(a x + b)ArcSin[a x + b])/a /;FreeQ[{a,b},x]


Int[ArcCos[a_ x_ +b_],x_]:= x ArcCos[a x + b] - (Sqrt[-a^2 x^2 - 2 a b x - b^2 + 1] + b ArcSin[a x + b])/a /;FreeQ[{a,b},x] 


Int[ArcTan[a_ x_ +b_],x_]:= -(Log[a^2x^2 + 2a b x + b^2 + 1] - 2(a x + b)ArcTan[a x + b])/(2a) /;FreeQ[{a,b},x]


Int[ArcCot[a_ x_ +b_],x_]:= (Log[a^2x^2 + 2a b x + b^2 + 1] - 2b ArcTan[a x + b])/(2a)+x ArcCot[a x + b]/;FreeQ[{a,b},x] 


Int[ArcSec[a_ x_ +b_],x_]:= x ArcSec[b + a x] - ((b + a x) Sqrt[(-1 + b^2 + 2 a b x + a^2 x^2)/(b + a x)^2] (b ArcTan[1/Sqrt[-1 + b^2 + 2 a b x + a^2 x^2]] + Log[2 (b + a x + Sqrt[-1 + b^2 + 2 a b x + a^2 x^2])]))/(a Sqrt[-1 + b^2 + 2 a b x + a^2 x^2]) /;FreeQ[{a,b},x] 


Int[ArcCsc[a_ x_ +b_],x_]:= x ArcCsc[b + a x] + ((b + a x) Sqrt[(-1 + b^2 + 2 a b x + a^2 x^2)/(b + a x)^2] (b ArcTan[1/Sqrt[-1 + b^2 + 2 a b x + a^2 x^2]] + Log[2 (b + a x + Sqrt[-1 + b^2 + 2 a b x + a^2 x^2])]))/(a Sqrt[-1 + b^2 + 2 a b x + a^2 x^2]) /;FreeQ[{a,b},x] 


Int[Log[a_ x_ +b_],x_]:= -x + (b Log[b + a x])/a + x Log[b + a x] /;FreeQ[{a,b},x] 


Int[E^(a_ x_ +b_),x_]:= E^(b + a x)/a /;FreeQ[{a,b},x] 


Int[c_^(a_ x_ +b_),x_]:= c^(b + a x)/(a Log[c]) /;FreeQ[{a,b,c},x]


Int[1/(a_x +b_),x_]:= Log[b + a x]/a /;FreeQ[{a,b},x]


Int[Sqrt[b_ + a_ x_], x_]  := (2 (b + a x)^(3/2))/(3 a)/;FreeQ[{a, b}, x]


Int[x_ Sqrt[b_ + a_ x_],x_]:= (2 Sqrt[b + a x] (-2 b^2 + a b x + 3 a^2 x^2))/(15 a^2) /;FreeQ[{a, b}, x] 


Int[1/(x_^2 +a_^2),x_] := ArcTan[x/a]/a /;FreeQ[{a},x] && a!=0


Int[1/(x_^2 -a_^2),x_] := -(ArcTanh[x/a]/a) /;FreeQ[{a},x] && a!=0


Int[1/(a_^3 +x_^3),x_]:= (2 Sqrt[3] ArcTan[(-a + 2 x)/(Sqrt[3] a)] + 2 Log[a + x] - Log[a^2 - a x + x^2])/(6 a^2) /;FreeQ[{a},x]


Int[1/(a_^3 -x_^3),x_]:= (2 Sqrt[3] ArcTan[(a + 2 x)/(Sqrt[3] a)] - 2 Log[-a + x] + Log[a^2 + a x + x^2])/(6 a^2) /;FreeQ[{a},x]


Int[x_/(a_^3 +x_^3),x_]:= (2 Sqrt[3] ArcTan[(-a + 2 x)/(Sqrt[3] a)] - 2 Log[a + x] + Log[a^2 - a x + x^2])/(6 a) /;FreeQ[{a},x] 


Int[x_/(a_^3 -x_^3),x_]:= (-2 Sqrt[3] ArcTan[(a + 2 x)/(Sqrt[3] a)] - 2 Log[-a + x] + Log[a^2 + a x + x^2])/(6 a) /;FreeQ[{a},x]


Int[x_^2/(a_^3 +x_^3),x_] := Log[a^3 + x^3]/3 /;FreeQ[{a},x]


Int[x_^2/(a_^3 -x_^3),x_] := -Log[a^3 - x^3]/3/;FreeQ[{a},x]


Int[1/(a_^4 +x_^4),x_]:= (-2 ArcTan[1 - (Sqrt[2] x)/a] + 2 ArcTan[1 + (Sqrt[2] x)/a] - Log[a^2 - Sqrt[2] a x + x^2] + Log[a^2 + Sqrt[2] a x + x^2])/(4 Sqrt[2] a^3)/;FreeQ[{a},x] 


Int[1/(a_^4 -x_^4),x_]:= ArcTan[x/a]/(2 a^3) - Log[-a + x]/(4 a^3) + Log[a + x]/(4 a^3) /;FreeQ[{a},x] 


Int[x_/(a_^4 +x_^4),x_]:= ArcTan[x^2/a^2]/(2 a^2) /;FreeQ[{a},x] 


Int[x_/(a_^4 -x_^4),x_] := ArcTanh[x^2/a^2]/(2 a^2) /;FreeQ[{a},x]


Int[x_^2/(a_^4 +x_^4),x_]:= (-2 ArcTan[1 - (Sqrt[2] x)/a] + 2 ArcTan[1 + (Sqrt[2] x)/a] + Log[a^2 - Sqrt[2] a x + x^2] - Log[a^2 + Sqrt[2] a x + x^2])/(4 Sqrt[2] a) /;FreeQ[{a},x]


Int[x_^2/(a_^4 -x_^4),x_]:= -ArcTan[x/a]/(2 a) - Log[-a + x]/(4 a) + Log[a + x]/(4 a) /;FreeQ[{a},x] 


Int[x_^3/(a_^4 -x_^4),x_]:= Log[a^4 + x^4]/4 /;FreeQ[{a},x] 


Int[x_^3/(a_^4 -x_^4),x_]:= -Log[a^4 - x^4]/4 /;FreeQ[{a},x] 


Int[x_ (a_ x_ +b_)^n_,x_]:= ((b + a x)^(1 + n) (-b + a (1 + n) x))/(a^2 (1 + n) (2 + n))  /;FreeQ[{a,b,n},x]&& n!=-1 && n!=-2


Int[x_/(a_ x_ +b_),x_]:= x/a - (b Log[b + a x])/a^2 /;FreeQ[{a,b},x] 


Int[x_/(a_ x_ +b_)^2,x_]:= (b/(b + a x) + Log[b + a x])/a^2 /;FreeQ[{a,b},x] 


Int[1/(x_ Sqrt[a_ x_ +b_]),x_]:= (-2 ArcTanh[Sqrt[b + a x]/Sqrt[b]])/Sqrt[b]  /;FreeQ[{a,b},x]


Int[Sqrt[a_ x_ +b_]/x_,x_]:= 2 Sqrt[b + a x] - 2 Sqrt[b] ArcTanh[Sqrt[b + a x]/Sqrt[b]] /;FreeQ[{a,b},x] 


Int[Sqrt[a_ x_ +b_]/x_^2,x_]:= -(Sqrt[b + a x]/x) - (a ArcTanh[Sqrt[b + a x]/Sqrt[b]])/Sqrt[b] /;FreeQ[{a,b},x] 


Int[1/(x_^2 Sqrt[a_ x_ +b_]),x_]:= -(Sqrt[b + a x]/(b x)) + (a ArcTanh[Sqrt[b + a x]/Sqrt[b]])/b^(3/2) /;FreeQ[{a,b},x] 


Int[1/(a_^2 +x_^2)^2,x_]:= ((a x)/(a^2 + x^2) + ArcTan[x/a])/(2 a^3) /;FreeQ[{a},x] 


Int[1/(a_^2 -x_^2)^2,x_]:= ((a x)/(a^2 - x^2) + ArcTanh[x/a])/(2 a^3)  /;FreeQ[{a},x]


Int[1/Sqrt[x_^2 +a_^2],x_]:= Log[2 (x + Sqrt[a^2 + x^2])] /;FreeQ[{a},x] 


Int[1/Sqrt[x_^2 -a_^2],x_]:= Log[2 (x + Sqrt[-a^2 + x^2])] /;FreeQ[{a},x] 


Int[Sqrt[a_^2 -x_^2],x_]:= (x Sqrt[a^2 - x^2] + a^2 ArcTan[x/Sqrt[a^2 - x^2]])/2 /;FreeQ[{a},x]


Int[Sqrt[x_^2 +a_^2],x_]:= (x Sqrt[a^2 + x^2])/2 + (a^2 Log[2 (x + Sqrt[a^2 + x^2])])/2/;FreeQ[{a},x] 


Int[Sqrt[x_^2 -a_^2],x_] := (x Sqrt[-a^2 + x^2])/2 - (a^2 Log[2 (x + Sqrt[-a^2 + x^2])])/2 /;FreeQ[{a},x]


Int[(x_^2 +a_)^(3/2),x_]:= Sqrt[a + x^2] ((5 a x)/8 + x^3/4) + (3 a^2 Log[2 (x + Sqrt[a + x^2])])/8 /;FreeQ[{a},x] 


Int[(x_^2 -a_)^(3/2),x_] := Sqrt[-a + x^2] ((-5 a x)/8 + x^3/4) + (3 a^2 Log[2 (x + Sqrt[-a + x^2])])/8 /;FreeQ[{a},x]


Int[1/(x_^2 +a_^2)^(3/2),x_]:= x/(a^2 Sqrt[a^2 + x^2]) /;FreeQ[{a},x] 


Int[1/(x_^2 -a_^2)^(3/2),x_]:= -(x/(a^2 Sqrt[-a^2 + x^2])) /;FreeQ[{a},x] 


Int[1/Sqrt[2 a_ x_ -x_^2],x_]:= ArcSin[(x-a)/a] /;FreeQ[{a},x] 


Int[Sqrt[2 a_ x_ -x_^2],x_]:= (x-a)/2 Sqrt[2 a x-x^2]+a^2/2 ArcSin[(x-a)/a] /;FreeQ[{a},x]


Int[x_ Sqrt[2 a_ x_ -x_^2],x_] := (x+a) (2 x-3 a) Sqrt[2 a x-x^2]/6+a^3/2 ArcSin[(x-a)/a] /;FreeQ[{a},x]


Int[Sqrt[2 a_ x_ -x_^2]/x_,x_]:= Sqrt[2 a x-x^2]+a ArcSin[(x-a)/a] /;FreeQ[{a},x] 


Int[Sqrt[2 a_ x_ -x_^2]/x_^2,x_]:= -2 Sqrt[(2 a-x)/x] -ArcSin[(x-a)/a] /;FreeQ[{a},x] 


Int[x_/Sqrt[2 a_ x_ -x_^2],x_]:= a ArcSin[(x-a)/a]-Sqrt[2 a x-x^2] /;FreeQ[{a},x] 


Int[1/(x_ Sqrt[2 a_ x_ -x_^2]),x_]:= -1/a Sqrt[(2 a-x)/x] /;FreeQ[{a},x] 


Int[Sqrt[(a_+x_)/(b_+x_)],x_]:= (Sqrt[(a + x)/(b + x)] (2 Sqrt[a + x] (b + x) + (a - b) Sqrt[b + x] Log[a + b + 2 x + 2 Sqrt[a + x] Sqrt[b + x]]))/(2 Sqrt[a + x])  /;FreeQ[{a,b},x]


Int[Sqrt[(a_-x_)/(b_+x_)],x_]:= (Sqrt[(a - x)/(b + x)] (2 (b + x) - ((a + b) Sqrt[b + x] ArcTan[(a - b - 2 x)/(2 Sqrt[a - x] Sqrt[b + x])])/Sqrt[a - x]))/2 /;FreeQ[{a,b},x]


Int[1/Sqrt[(x_-a_) (b_-x_)],x_] := -((Sqrt[b - x] Sqrt[-a + x] ArcTan[(a + b - 2 x)/(2 Sqrt[b - x] Sqrt[-a + x])])/Sqrt[(a - x) (-b + x)]) /;FreeQ[{a,b},x]


Int[1/(x_^4+a_^4),x_]:= (-2 ArcTan[1 - (Sqrt[2] x)/a] + 2 ArcTan[1 + (Sqrt[2] x)/a] - Log[a^2 - Sqrt[2] a x + x^2] + Log[a^2 + Sqrt[2] a x + x^2])/(4 Sqrt[2] a^3) /;FreeQ[{a},x] 


Int[1/(a_^4-x_^4),x_]:= ArcTan[x/a]/(2 a^3) - Log[-a + x]/(4 a^3) + Log[a + x]/(4 a^3) /;FreeQ[{a},x] 


Int[x_^n_ Log[a_ x_],x_]:= (x^(1 + n) (-1 + (1 + n) Log[a x]))/(1 + n)^2 /;FreeQ[{a,n},x] 


Int[b_^(a_ x_),x_] := b^(a x)/(a Log[b]) /;FreeQ[a,x]


Int[E^(a_ x_),x_]:= E^(a x)/a  /;FreeQ[{a},x] 


Int[b_^(a_ x_),x_]:= b^(a x)/(a Log[b])  /;FreeQ[{a,b},x]


Int[E^(a_ x_) Sin[b_ x_], x_]:= (E^(a x) (-(b Cos[b x]) + a Sin[b x]))/(a^2 + b^2) /;FreeQ[{a,b},x] 


Int[E^(a_ x_) Cos[b_ x_], x_]:= (E^(a x) (a Cos[b x] + b Sin[b x]))/(a^2 + b^2) /;FreeQ[{a,b},x] 


Int[1/(x_+a_),x_]:=  Log[x+a] /;FreeQ[a,x] 


Int[1/(a_ x_ +b_),x_]:=  Log[a x+b]/a /;FreeQ[{a,b},x] 


Int[x_(E^x_),x_] := -E^x + x(E^x)


Int[x_(E^(x_+a_)),x_]:= x E^x -E^x+x^2 E^a/2 /;FreeQ[a,x] 


Int[x_(E^(a_ x_)),x_]:= x (E^(a x))/a-E^(a x)/a^2 /;FreeQ[a,x] 


Int[x_(E^(a_ x_+b_)),x_]:= x (E^(a x+b))/a -E^(a x+ b)/a^2 /;FreeQ[{a,b},x] 


Int[x_/Sqrt[a_+x_^2],x_]:= Sqrt[a+x^2]/;FreeQ[a,x]


Int[a_ x_/Sqrt[b_+x_^2],x_]:= a Sqrt[b+ x^2] /;FreeQ[{a,b},x]


Int[x_/Sqrt[a_+b_ x_^2],x_] := Sqrt[a+b x^2]/b /;FreeQ[{a,b},x]&&NonzeroQ[b]


Int[a_ x_/Sqrt[b_+c_ x_^2],x_] := a Sqrt[b+c x^2]/c /;FreeQ[{a,b,c},x]&&NonzeroQ[c]


Int[Cos[x_]^n_,x_] := Cos[x]^(n-1)*Sin[x]/n + Dist[n-1/n,Int[Cos[x]^(n-2),x]]/;FreeQ[n,x]&&IntegersQ[n]&&n>1


Int[Sin[x_]^n_,x_] := -Sin[x]^(n-1)*Cos[x]/n + Dist[n-1/n,Int[Sin[x]^(n-2),x]]/;FreeQ[n,x]&&IntegersQ[n]&&n>1


Int[Tan[x_]^n_,x_] := -Tan[x]^(n-1)/(n-1)-Int[Tan[x]^(n-2),x]/;FreeQ[n,x]&&IntegersQ[n]&&n>1
