(* ::Package:: *)

(*IntTable*)
stageII[Sin[x],x]


(*intSubPow*)
stageII[x^3 Sin[x^2],x]
stageII[x^7/(x^12+1),x]


(*intSubFra*)
stageII[Cos[Sqrt[x]],x]
stageII[x Sqrt[x+1],x]
stageII[1/(x^(1/2)-x^(1/3)),x]
stageII[Sqrt[(x+1)/(2x+3)],x]


(*intSubBin*)
stageII[x^4(1-x^2)^(-5/2),x]
stageII[x^(1/2)*(1+x)^(5/2),x](*\:5148\:7ecfFra?*)


(*intSubRfs*)
stageII[x Log[E,x],x]
stageII[1/(x^2+2x+1)*Log[x^2+2x],x]
