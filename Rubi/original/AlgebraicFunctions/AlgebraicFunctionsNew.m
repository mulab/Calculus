(* ::Package:: *)

Int[Sqrt[(a_+b_ x_^n_)/x_^2],x_] := 2 *x Sqrt[(a+b x^n)/x^2]*(Sqrt[a+b x^n]-Sqrt[a]*ArcTanh[Sqrt[a+b x^n]/Sqrt[a]])/(n*Sqrt[a+b x^n])/;FreeQ[{a,b,n},x]


Int[1/Sqrt[(a_+x_) (b_+x_)],x_] := ArcTanh[(a+b+2 x)/(2 Sqrt[a b+(a+b) x+x^2])]/;FreeQ[{a,b},x]


Int[1/Sqrt[(a_-x_) (b_+x_)],x_] := -ArcTan[(a-b-2 x)/(2 Sqrt[a b+(a-b) x-x^2])]/;FreeQ[{a,b},x]


Int[(Sqrt[1-x_]+Sqrt[1+x_])^2/x_,x_] :=2 Sqrt[1-x] Sqrt[1+x]-4 ArcTanh[Sqrt[1-x]/Sqrt[1+x]]+2 Log[x]


Int[x_/(x_+Sqrt[x_^6]),x_] := ((x^3+Sqrt[x^6]) ArcTan[x]+(x^3-Sqrt[x^6]) ArcTanh[x])/(2 x^3)


Int[1/(x_ (a_+b_ x_)^(1/3)),x_] := (Sqrt[3] ArcTan[(2 (1/2+(a+b x)^(1/3)/a^(1/3)))/Sqrt[3]]+Log[-a^(1/3)+(a+b x)^(1/3)]-1/2 Log[a^(2/3)+a^(1/3) (a+b x)^(1/3)+(a+b x)^(2/3)])/a^(1/3)/;FreeQ[{a,b},x]&&NonzeroQ[a]&&NonzeroQ[b]


(*Int[x_^(13/2)/Sqrt[1+x_^5],x_] :=1/5 x^(5/2) Sqrt[1+x^5]-1/5 ArcSinh[x^(5/2)]*)


(*Int[1/(x_+Sqrt[-2+3 x_-x_^2]),x_] := ArcTan[Sqrt[-2+3 x-x^2]/(1-x)]+(3 ArcTan[(-1+x+2 Sqrt[-2+3 x-x^2])/(Sqrt[7] (-1+x))])/Sqrt[7]-1/2 Log[1/(-1+x)]+1/2 Log[(x+Sqrt[-2+3 x-x^2])/(-1+x)]*)
