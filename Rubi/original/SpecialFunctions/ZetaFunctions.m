(* ::Package:: *)

(* ::Code:: *)
Int[Zeta[2,a_.+b_.*x_],x_Symbol] :=
(Print["Int(1th)@ZetaFunctions.m"];
  Int[PolyGamma[1,a+b*x],x]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[Zeta[s_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(2th)@ZetaFunctions.m"];
  -Zeta[s-1,a+b*x]/(b*(s-1))) /;
FreeQ[{a,b,s},x] && NonzeroQ[s-1] && NonzeroQ[s-2]

(* ::Code:: *)
Int[x_^m_.*Zeta[2,a_.+b_.*x_],x_Symbol] :=
(Print["Int(3th)@ZetaFunctions.m"];
  Int[x^m*PolyGamma[1,a+b*x],x]) /;
FreeQ[{a,b},x] && RationalQ[m]

(* ::Code:: *)
Int[x_^m_.*Zeta[s_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(4th)@ZetaFunctions.m"];
  -x^m*Zeta[s-1,a+b*x]/(b*(s-1)) +
  Dist[m/(b*(s-1)),Int[x^(m-1)*Zeta[s-1,a+b*x],x]]) /;
FreeQ[{a,b,s},x] && RationalQ[m] && m>0 && NonzeroQ[s-1] && NonzeroQ[s-2]

(* ::Code:: *)
Int[x_^m_.*Zeta[s_,a_.+b_.*x_],x_Symbol] :=
(Print["Int(5th)@ZetaFunctions.m"];
  x^(m+1)*Zeta[s,a+b*x]/(m+1) +
  Dist[b*s/(m+1),Int[x^(m+1)*Zeta[s+1,a+b*x],x]]) /;
FreeQ[{a,b,s},x] && RationalQ[m] && m<-1 && NonzeroQ[s-1] && NonzeroQ[s-2]

