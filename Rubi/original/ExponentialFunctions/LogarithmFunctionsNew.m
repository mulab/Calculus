(* ::Package:: *)

Int[Log[a_+b_ x_^m_]/x_, x_] := (Log[-((b x^m)/a)] Log[a+b x^m])/m+PolyLog[2,1+(b x^m)/a]/m/;FreeQ[{a,b,m},x]&&NonzeroQ[m]&&NonzeroQ[a]


Int[Log[a_+b_ x_^2]^2/x_^3, x_] := (b Log[-((b x^2)/a)] Log[a+b x^2])/a-((a+b x^2) Log[a+b x^2]^2)/(2 a x^2)+(b PolyLog[2,1+(b x^2)/a])/a/;FreeQ[{a,b},x]&&NonzeroQ[a]


Int[Log[(c_ x_)/(a_+b_ x_)]^3, x_] :=  (3 a Log[-(a/(b x))] Log[(c x)/(a+b x)]^2)/b+((a+b x) Log[(c x)/(a+b x)]^3)/b-(6 a Log[(c x)/(a+b x)] PolyLog[2,1+a/(b x)])/b-(6 a PolyLog[3,1+a/(b x)])/b/;FreeQ[{a,b,c},x]&&NonzeroQ[b]


Int[Log[(a_+b_ x_)^2/x_^2]^3, x_] :=  ((a+b x) Log[(b+a/x)^2]^3)/b-(6 a Log[(b+a/x)^2]^2 Log[-(a/(b x))])/b-(24 a Log[(b+a/x)^2] PolyLog[2,1+a/(b x)])/b+(48 a PolyLog[3,(b+a/x)/b])/b/;FreeQ[{a,b},x]&&NonzeroQ[b]
