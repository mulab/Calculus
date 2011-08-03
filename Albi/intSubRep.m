(* ::Package:: *)

(*This method is applicable whenever the integrand is of the form R(x)E^P(x),
where R(x) is a rational function *)
(*the method 7 of SIN StageII, Moses*)
(*Shao Qiming*)
intSubRep[f_,x_]:=Module[
{e=f,R,P,eP,a={},U={}},
(*\:5224\:65adR\:662f\:5426\:4e3a\:6709\:7406\:51fd\:6570\:ff0c\:63d0\:53d6R\:548cP*)
SetDirectory[NotebookDirectory[]];
Import["..\\utility\\RationalQ.m"];
If[Head[e]===Times,(*then*)
eP=e[[1]];
If[!MatchQ[eP,E^_],Print[{eP}];Return["NotMatch"]];
R=Simplify[e/eP];(**)
If[!RationalQ[R],Print[{R}];Return["NotMatch"]];
P=eP[[2]],(*else*)
If[Head[e]===Power,eP=e;P=e[[2]];R=1]
];
(*\:5229\:7528R\:6784\:9020S\:ff0cQ\:548ccx*)
Q=Denominator[R];
Rn=Numerator[R];
If[Length[Rn]>1,cx=Rn[[-1]],cx=Rn];(*Get cx^m_1*)
S=Rn-cx;
(*If[Head[cx]===Times,c=cx[[1]],(*else*)
	If[Head[cx]===Power,c=1,(*else*)
	If[FreeQ[cx,x],c=cx,c=1]
]](*Get const "c", not necessary*)*)
(*Print[{cx,Q,S}];*)
(*\:6709\:5173\:8868\:8fbe\:5f0f\:7684\:6392\:5e8f*)
(*construct T*)
(*at=cx/D[P,x]/Q;
Pb=R-D[P,x]*at-D[at,x];
T=Pb*Q;
Print[{"Step1",cx,at,T,at*E^P}];
(*\:63d0\:53d6T\:7684\:591a\:9879\:5f0f\:548c\:6709\:7406\:5f0f*)
Print[dapart[T,x]];
{T,U}=dapart[T,x];
If[Length[T]>1,cx=T[[-1]],cx=T];(*Get cx^m_1*)
at2=cx/D[P,x]/Q;
Print[Simplify[(at+at2)*E^P]];*)
at=cx/D[P,x]/Q;
Pb=R-D[P,x]*at-D[at,x];
TU=Pb*Q;
AppendTo[a,at];
(*Print[{TU,"TU"}];*)
{T,Ut}=dapart[TU,x];
AppendTo[U,Ut];
(*Print[{T,Ut}];*)
While[T!=0,
If[Length[T]>1,cx=T[[-1]],cx=T];(*Get cx^m_1*)
R=T/Q;
at=cx/D[P,x]/Q;
Pb=R-D[P,x]*at-D[at,x];
AppendTo[a,at];
TU=Pb*Q;
{T,Ut}=dapart[TU,x];
AppendTo[U,Ut];
(*Print[{T,U,"xuanhuan"}]*)
];
(*Print[{a,U,"hh"}];*)
If[Total[U]!=0,Return["NoClose"],Return[{Simplify[Total[a]]*E^P,x}],Return["NoClose"]];
]


(*dapart\:5c06\:4e00\:4e2a\:5173\:4e8ex\:7684\:8868\:8fbe\:5f0f\:5206\:89e3\:6210\:5173\:4e8ex\:7684\:591a\:9879\:5f0f\:548c\:6709\:7406\:5f0f*)
dapart[f_,x_]:=Module[
{e=f,a,c,tt,len},
a=Apart[Simplify[e]];
c=0;
(*\:4ee5\:4e0b\:5904\:7406\:5355\:9879*)
If[Length[a]==0,Return[{a,0}]];
If[Head[a]===Power,If[a[[2]]<0,Return[{0,a}],Return[{a,0}]]];
If[Head[a]===Times,tt=a[[-1]];
	If[Head[tt]===Power,If[tt[[2]]<0,Return[{0,a}],Return[{a,0}]],
	Return[{a,0}]];
];
(*\:4ee5\:4e0b\:5904\:7406\:591a\:9879*)
For[tt=1,tt<=Length[a],tt=tt+1,
thispart = a[[tt]];
If[Head[thispart]===Times,
thispart=thispart[[-1]]
];
If[Head[thispart]===Power,
If[thispart[[2]]<0,Continue[]]
];
c=c+a[[tt]];
];
Return[{c,a-c}];
]



(*intSubRep[x E^x,x]
intSubRep[x/(x+1)^2*E^x,x]
intSubRep[(1+2 x^2)*E^(x^2),x]
intSubRep[E^(x^2),x]
intSubRep[E^x*(1/x+1/x^2),x]

*)


