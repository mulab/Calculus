(* ::Package:: *)

Int[1/(1+Sec[a_+b_ x_]),x_] := x-Sin[a+b x]/(b (1+Cos[a+b x])) /;FreeQ[{a,b},x]&&NonzeroQ[b]


(*Sin[x]Tan[nx]*)


Int[Sqrt[Sec[a_+b_ x_]^2],x_] := ArcSinh[Tan[a+b x]]/b /;FreeQ[{a,b},x]&&NonzeroQ[b]


Int[Sqrt[Sec[x_]^2],x_] := ArcSinh[Tan[x]]


Int[Sqrt[Csc[x_]^2],x_] := -ArcCsch[Tan[x]]


Int[Sqrt[1+Sec[x_]],x_] := (2 ArcTanh[Sqrt[1-Sec[x]]] Tan[x])/(Sqrt[1-Sec[x]] Sqrt[1+Sec[x]])


Int[Sqrt[1+Csc[x_]],x_] := -((2 ArcTanh[Sqrt[1-Csc[x]]] Cot[x])/(Sqrt[1-Csc[x]] Sqrt[1+Csc[x]]))


Int[Sqrt[c_*Cos[x_-d_]],x_] := (2 Sqrt[c Cos[d-x]] EllipticE[(d-x)/2,2])/Sqrt[Cos[d-x]]/;FreeQ[{c,d},x]


Int[Sin[x_]/Sqrt[a_+b_ Sin[x_]^2],x_] := ArcTan[(Sqrt[a+b-b Cos[x]^2] Sec[x])/Sqrt[b]]/Sqrt[b]/;FreeQ[{a,b},x]&&NonzeroQ[b]



Int[Cot[x_]/Sqrt[a_+b_ Tan[x_]^2+c_ Tan[x_]^4],x_] := -(ArcTanh[(2 Sqrt[a] Sqrt[a+b Tan[x]^2+c Tan[x]^4])/(2 a+b Tan[x]^2)]/(2 Sqrt[a]))+ArcTanh[(2 Sqrt[a-b+c] Sqrt[a+b Tan[x]^2+c Tan[x]^4])/(2 a-b+(b-2 c) Tan[x]^2)]/(2 Sqrt[a-b+c])/;FreeQ[{a,b,c},x]&&NonzeroQ[a]&&NonzeroQ[a-b+c]
