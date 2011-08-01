(* ::Package:: *)

(* Method 10 in Stage II, (8)Rational functions of logarithms*)
(* Last by ivan on 16:56 Aug 1, 2011. Email: ma_wan _li .6209@163.com *)
(* The codes that are down earlier is at bottom of this file*)
(* Principle: if the integrand is f(log(x))dx, substitude log(x) by y
	and output f(y)exp(y)dy  *)
intSubLog[f_,x_]:=Module[
	{e1,e2,e3,e4,a,b,e},
	e1 = f/.Log[x]->log1;
	e2 = f/.Log[x + b_]->log2;
	e3 = f/.Log[a_ x]->log3;
	e4 = f/.Log[a_ x + b_]->log4;
	If[FreeQ[e1,x] ,
		a=1;b=0;e=f/.Log[x]->y,
		If[FreeQ[e2,x],
			a=1;b=Extract[f,Drop[Position[f,x][[1]],-1]][[1]];e=f/.Log[b + x]->y,
			If[FreeQ[e3,x],
				a=Extract[f,Drop[Position[f,x][[1]],-1]][[1]];b=0;e=f/.Log[a x]->y,
				If[FreeQ[e4,x],
					a=Extract[f,Drop[Position[f,x][[1]],-1]][[1]];
					b=Extract[f,Drop[Position[f,x][[1]],-2]][[1]];
					e=f/.Log[b + a x]->y;
				];
			];
		];
	];
	e=f/.Log[b + a x]->y;
	If[!FreeQ[e,x],Return["NotMatch"];];
	If[!FreeQ[a,x],Return["NotMatch"];];
	If[!FreeQ[b,x],Return["NotMatch"];];
	Return[{e Exp[y],y,Log[a x + b]}];
]


intSubLog[Log[x+2]/(Log[x+2]+1)^2,x]
intSubLog[1/Log[x],x]


(*
(* Moses method 10
    Rational function times an elemently function of log[c,a+bx]   *)

intSubLog[f_,x_]:=Module[

(*\:6211\:5c06log\:5185\:7684\:8868\:8fbe\:5f0f\:5206\:4e3a4\:79cd\:ff1ax\:ff0cx+b\:ff0cax\:ff0cax+b\:ff1b\:5206\:522b\:5bf9\:5e94\:ff1apos1\:ff0cpos2\:ff0cpos3\:ff0cpos4\:ff0c\:82e5\:4e0d\:662f4\:79cd\:5f62\:5f0f\:4e4b\:4e00
\:5219\:663e\:7136\:4e0d\:6ee1\:8db3\:6761\:4ef6*)
(*
  \:ff081\:ff09\:540c\:65f6\:82e5\:6709\:4e24\:4e2a\:4e0d\:540c\:7684Log[ax+b]\:ff0cLog[cx+d]\:6211\:4eec\:89c6\:4e3a\:4e0d\:7b26\:5408\:6761\:4ef6\:3002
  \:9996\:5148\:6211\:5f15\:5165c\:6765\:6807\:8bb0\:524d\:9762\:662f\:5426\:5df2\:7ecf\:5b58\:5728\:6ee1\:8db3\:6761\:4ef6\:7684\:60c5\:51b5\:3002
  \:82e5\:524d\:9762\:5df2\:7ecf\:5b58\:5728\:6ee1\:8db3\:6761\:4ef6\:7684\:60c5\:5f62\:ff0c\:5219\:82e5\:53c8\:5b58\:5728\:4e00\:79cd\:6ee1\:8db3\:6761\:4ef6\:7684\:60c5\:5f62\:ff0c\:5219\:6ee1\:8db3\:60c5\:5f62 \:ff081\:ff09\:ff0c\:89c6\:4e3a\:4e0d\:6ee1\:8db3\:6761\:4ef6\:3002
  \:8fd9\:6837\:53ef\:4ee5\:6392\:9664\:7ec4\:95f4\:6ee1\:8db3\:6761\:4ef6\:4e00\:7684\:60c5\:5f62\:3002
  \:7136\:540e\:6211\:518d\:5904\:7406\:7ec4\:5185\:6ee1\:8db3\:60c5\:5f62 \:ff081\:ff09\:7684\:60c5\:51b5\:3002
*)
	{Test=f,pos,pos1,pos2,pos3,pos4,c,a,b,pow,Tst1},
	pos1=Position[Test,Log[x]/;FreeQ[d,x]];
    pos2=Position[Test,Log[d_+x]/;FreeQ[d,x]];
    pos3=Position[Test,Log[e_*x ]/;FreeQ[e,x]];
    pos4=Position[Test,Log[e_ *x+ d_]/;FreeQ[e,x]&&FreeQ[d,x]];
    c=0;
   If[pos1=={},,
        If[c==1,Return["NotMatch"],
       Test=Test/.x->Exp[y];
		Test=ReplaceAll[Test,{Log[E^z_]->z}];
        Tst1=ReplaceAll[Test,{E^z_->z}];
        pos=Position[Tst1,Log[d_]/;!FreeQ[d,y]];
        If[pos!={},Return["NotMatch"];];
         Test=Test Exp[y];
         c=1
         ]
     ];
If[pos2=={},,If[c==1,Return ["NotMatch"],
     pow=Extract[Test,pos2[[1]]];
      a=Level[pow,2][[1]];
 
      Test=Test/.x->(Exp[y]-a);
      Test=ReplaceAll[Test,{Log[E^z_]->z}];
       Tst1=ReplaceAll[Test,{E^z_->z}];
       pos=Position[Tst1,Log[d_]/;!FreeQ[d,y]];
       If[pos!={},Return["NotMatch"];];
       Test=Test Exp[y];
       c=1
       ]
];
  If[pos3=={},,
     If[c==1,Return["NotMatch"],
      pow=Extract[Test,pos3[[1]]];
      a=Level[pow,2][[1]];
 
      Test=Test/.x->(Exp[y]/a);
      Test=ReplaceAll[Test,{Log[E^z_]->z}];
       Tst1=ReplaceAll[Test,{E^z_->z}];
      pos=Position[Tst1,Log[d_]/;!FreeQ[d,y]];
       If[pos!={},Return["NotMatch"];];
       Test=(Test Exp[y])/a;
        c=1
         ]
];
If[pos4=={},,If[c==1,Return["NotMatch"],
     pow=Extract[Test,pos4[[1]]];
     a=Level[pow,2][[1]];
     b=Level[pow,3][[2]];
     Test=Test/.x->((Exp[y]-a)/b);
     Test=ReplaceAll[Test,{Log[E^z_]->z}];
     Tst1=ReplaceAll[Test,{E^z_->z}];
     pos=Position[Tst1,Log[d_]/;!FreeQ[d,y]];
     If[pos!={},Return["NotMatch"];];
     
        
 Test=(Test Exp[y])/b;
     c=1
       ] 
];
If[c==1,Return[{Test,y}];,
Return ["NotMatch"]];
	]
*)
