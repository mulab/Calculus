(* ::Package:: *)

(*\:6211\:5c06\:7a0b\:5e8f\:5206\:4e3a3\:6bb5\:ff0c\:5206\:522b\:5224\:65ad\:662f\:5426\:6ee1\:8db3 \[OpenCurlyDoubleQuote]R Log[s]\[CloseCurlyDoubleQuote] ; \[OpenCurlyDoubleQuote]R ArcSin[s]\[CloseCurlyDoubleQuote] ; \[OpenCurlyDoubleQuote]R Tan[S]\[CloseCurlyDoubleQuote],\:4e09
\:79cd\:5f62\:5f0f\:ff0c\:5e76\:5206\:522b\:5904\:7406\:3002*)
intSubRfs[f_,x_]:=Module[
{Test=f,a,b,c,d,t,e,pow,pos1,pos2,pos3},
pos1=Position[Test, Log[d_]/;!FreeQ[d,x]];(*\:6700\:7ec8\:ff0cFreeQ[]\:4f1a\:53d8\:6210\:5224\:65ad\:662f\:5426\:4e3a\:6709\:7406\:51fd\:6570*)
pos2=Position[Test, ArcSin[d_]/;!FreeQ[d,x]];
pos3=Position[Test, ArcTan[d_]/;!FreeQ[d,x]];
(*\[OpenCurlyDoubleQuote]R Log[s]\[CloseCurlyDoubleQuote]*)
If[pos1=={},pow=1,
    If[pos1=={{}},a=Test;b=1,a=Extract[Test,pos1[[1]]];
  b=Test/a;];
 
(*\:5224\:65adb\:662f\:5426\:662f\:6709\:7406\:51fd\:6570*)
  t=Extract[a,1];
(*\:5224\:65adt\:662f\:5426\:662f\:6709\:7406\:51fd\:6570*)
  c=Integrate[b,x];
  d=-c D[t,x]/t;
  t=c*a;
Return[{d,x,x,t}];
];
(*\[OpenCurlyDoubleQuote]R ArcSin[s]\[CloseCurlyDoubleQuote]*)
If[pos2=={},pow=1,

  If[pos2=={{}},a=Test;b=1,a=Extract[Test,pos2[[1]]];
  b=Test/a;];
  t=Extract[a,1];
  c=Integrate[b,x];
  d=-c D[t,x]/Sqrt[1-t^2];
  
  t=c*a;

Return[{d,x,x,t}];
];

(*\[OpenCurlyDoubleQuote]R Tan[S]\[CloseCurlyDoubleQuote]*)
If[pos3=={},pow=1,
    If[pos3=={{}},a=Test;b=1,a=Extract[Test,pos3[[1]]];
  b=Test/a;];
  t=Extract[a,1];
  c=Integrate[b,x];
  d=-c D[t,x]/(t^2+1);

  
  t=c*a;
Return[{d,x,x,t}];

];


Return["NotMatch"];
]



(*IntSubRfs[Log[y],y]
IntSubRfs[ArcTan[y],y]
IntSubRfs[ArcSin[x],x]
IntSubRfs[y Log[y],y]
IntSubRfs[y^2* ArcTan[y],y]
IntSubRfs[y ArcSin[y],y]
IntSubRfs[Log[x^2+2x]/(x^2+2x+1),x]
*)



