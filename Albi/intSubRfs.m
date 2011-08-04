(* ::Package:: *)

(*the method 9 of Stage II Moses*)
(*Shao Qiming & Zhang Junlin*)
(*\:6211\:5c06\:7a0b\:5e8f\:5206\:4e3a3\:6bb5\:ff0c\:5206\:522b\:5224\:65ad\:662f\:5426\:6ee1\:8db3 "R Log[s]" ; "R ArcSin[S]" ; "R Tan[S]",\:4e09
\:79cd\:5f62\:5f0f\:ff0c\:5e76\:5206\:522b\:5904\:7406\:3002*)
intSubRfs[f_,x_]:=Module[
{e=f,R,Fs,T,d,S,pos1,pos2,pos3},
(*SetDirectory[NotebookDirectory[]];*)
(*Set Package Diretory*)
(*Import["..\\Utility\\RationalQ.m"];*)
(*Print[RationalQ[x^(1/2),{x}]];
Print[RationalQ[x^2,{x}]];*)(*Import test*)
(*Import[".\\intSubRat.m"];*)
(*Print[intSubRat[x^2,x]];*)

(*"R Log[s]"*)
pos1=Position[e, Log[d_]/;Calculus`Utility`RationalQ[d,{x}]];(*\:5224\:65ad\:662f\:5426\:4e3a\:6709\:7406\:51fd\:6570*)
If[pos1!={},
    If[pos1=={{}},Fs=e;R=1,Fs=Extract[e,pos1[[1]]];
  R=e/Fs];(*Fs=F(S),R=R*)
If[!Calculus`Utility`RationalQ[R,{x}],Return["NotMatch"]];
(*\:5224\:65adR\:662f\:5426\:662f\:6709\:7406\:51fd\:6570*)
  S=Extract[Fs,1];(*t=S*)
If[!Calculus`Utility`RationalQ[S,{x}],Return["NotMatch"]];
(*\:5224\:65adS\:662f\:5426\:662f\:6709\:7406\:51fd\:6570*)
T=Calculus`Albi`SIN[R,x];(*c\:662fT\:ff0c\:4e3aR\:7684\:79ef\:5206*)
If[T==="NotMatch"||!Calculus`Utility`RationalQ[T,x],Return["NotMatch"]];
 (* c=Integrate[b,x];*)
  d=-T D[S,x]/S;
  S=T*Fs;
Return[{S+Calculus`Albi`SIN[d,x],x}](*d\:4e3a\:5206\:90e8\:79ef\:5206\:4e2d\:8fd8\:9700\:79ef\:5206\:7684\:90e8\:5206\:ff0cS\:4e3a\:5df2\:7ecf\:79ef\:597d\:7684\:90e8\:5206\:ff0c
\:6700\:7ec8\:79ef\:5206\:4e3aS+Integrate[d,x]*)
];

(*"R ArcSin[s]"*)
pos2=Position[e, ArcSin[d_]/;Calculus`Utility`RationalQ[d,{x}]];
If[pos2!={},
  If[pos2=={{}},Fs=e;R=1,Fs=Extract[e,pos2[[1]]];
  R=e/Fs];
If[!Calculus`Utility`RationalQ[R,{x}],Return["NotMatch"]];
(*\:5224\:65adb\:662f\:5426\:662f\:6709\:7406\:51fd\:6570*)
  S=Extract[Fs,1];
If[!Calculus`Utility`RationalQ[S,{x}],Return["NotMatch"]];
(*\:5224\:65adt\:662f\:5426\:662f\:6709\:7406\:51fd\:6570*)
T=Calculus`Albi`SIN[R,x];
 (* c=Integrate[b,x];*)
If[T==="NotMatch"||!Calculus`Utility`RationalQ[T,x],Return["NotMatch"]];
  d=-T D[S,x]/Sqrt[1-S^2];  
  S=T*Fs;
Return[{S+Calculus`Albi`SIN[d,x],x}];
];

(*"R Tan[S]"*)
pos3=Position[e, ArcTan[d_]/;Calculus`Utility`RationalQ[d,{x}]];
If[pos3!={},
    If[pos3=={{}},Fs=e;R=1,Fs=Extract[e,pos3[[1]]];
  R=e/Fs];
If[!Calculus`Utility`RationalQ[R,{x}],Return["NotMatch"]];
(*\:5224\:65adb\:662f\:5426\:662f\:6709\:7406\:51fd\:6570*)
  S=Extract[Fs,1];
(*\:5224\:65adt\:662f\:5426\:662f\:6709\:7406\:51fd\:6570*)
If[!Calculus`Utility`RationalQ[S,{x}],Return["NotMatch"]];
T=Calculus`Albi`SIN[R,x];
(*c=Integrate[b,x];*)
If[T==="NotMatch"||!Calculus`Utility`RationalQ[T,x],Return["NotMatch"]];
d=-T D[S,x]/(S^2+1);
 S=T*Fs;
Return[{S+Calculus`Albi`SIN[d,x],x}];
];

Return["NotMatch"];
]



(*intSubRfs[Log[y],y]
intSubRfs[ArcTan[y],y]
intSubRfs[ArcSin[x],x]*)
(*intSubRfs[y^2* ArcTan[y+1]+1,y]*)
(*\:8fd9\:4e9b\:4f8b\:5b50\:5728StageI\:5c31\:5df2\:7ecf\:89e3\:51b3\:4e86\:ff0c\:90fd\:4e0d\:5e94\:8be5\:5b58\:5728\:4e86*)
intSubRfs[x Log[x],x]
intSubRfs[x ArcSin[x^2],x]
intSubRfs[Log[x^2+2x]/(x^2+2x+1),x]
intSubRfs[x^2 ArcTan[x],x]





