(* ::Package:: *)

(* Integration of Elementary Function, algorithms from book 
   Symbolic Integration, by M. Bronstein 
   
   Authors: Luis A. Medina and Sasha Pavlyk
   
   Mathematica Version: 6.1
   
   Comments: I'm not using algorithms that say "slow" at the beginning.  If an 
   algorithm has a version that says "fast" at the begging then I'm using it.  
   The "slow" versions work and I keep them in case anything goes wrong
   with the faster versions (kind of a back up). 
   
   *)


(**************** Chapter 2 ***********************)
HermiteReduce[n_, d_,x_] := 
(*Given a A,D in Q[x] with D nonzero and coprime with A,
  return g,h in Q (x) such that A/D = dg/dx+h and h has a
  squarefree denominator*)
 Module[{Dm, Ds, b, c, a,  Dm2, Dms, g, dd,p,cont},
    g = 0;
    {p, a} = PolyDivide[n,d,x];
    {cont,dd} = PolyContentPP[d,x];
    Dm = PolynomialGCD[dd, D[dd, x]];
    Ds = PolynomialQuotient[dd,Dm,x];
    While[deg[Dm, x] > 0,
     Dm2 = PolynomialGCD[Dm, D[Dm, x]];
     Dms = PolynomialQuotient[Dm,Dm2,x] ;
     {b, c} = fastExtendedEuclidean[
     				PolynomialQuotient[-Ds D[Dm, x],Dm,x], (* exact division *)
     				Dms, a,x];
     a = c - PolynomialQuotient[D[b, x] Ds, Dms, x];
     g = g + b/Dm;
     Dm = Dm2
     ];
    {g + PolyInt[p,x], Together[a/(cont*Ds)]}
   ]

HermiteReduce[R_,x_]:=
(* Final version of HermiteReduce *)
Module[{num, den},
	{num, den} = NumeratorDenominator[R];
	HermiteReduce[num, den, x]
];

Clear[IntRationalLogPart];

IntRationalLogPart[A_,d_,x_]:=
(* Lazard - Rioboo - Trager algorithm. 
   
   Given A,d in Q[x] with deg (A)<deg (d), d nonzero, squarefree and coprime
   with A, return Integrate[A/d,x] *)
   Module[{a,j,Res,R,m,i,ii,t,Qlist,list,n,AA,q,sol,sum,L, res,s},
   	list = fastSubResultantPRS[d, A - t D[d, x], x]; 
   	Res = First[list];
   	R = Last[list]; 
   	Qlist = SquareFree[Res];
   	n = Length[Qlist];
   	i = 0;
   	res = 0;
   	Scan[Function[q, 
   		If[Last[q] == deg[d,x],
   			s = d,
   			s = Cases[R,y_ /; deg[y,x] == Last[q] ][[1]];
   			AA =  SquareFree[lc[ s,x ]];
   			s = Fold[PolynomialQuotient[#1,PolynomialGCD[First[#2],
   					  First[q]^Last[#2]],t]&, s, AA];
   		];
   		res += Function[{Q,S},
   		     Table[
   		       RootSum[ 
   				Function[Evaluate[Q1/.t->#]] , 
   				Function[Evaluate[# Log[S/.t->#]]]
   		      ] , {Q1, First /@ FactorList[Q] } ]//Total
   	    ][ First[q], s ];
   	], Qlist];
	res
   ]	

IntRationalLogPart[A_,x_]:= Module[{num, den},
	{num, den} = NumeratorDenominator[A];
	IntRationalLogPart[num, den, x]
];
(*First /@ DeleteCases[FactorList[Q],u_/;FreeQ[u,t]]*)

(* Assumptions: degree (num) < degree (den), den != 0, and den is squarefree and coprime with num *)
LazardRiobooTrager[num_, den_, x_] /; PolynomialQ[num,x] && PolynomialQ[den,x] && Exponent[num,x]<Exponent[den,x] :=
 Module[{res,t,qq,a,s,nmtd,rr}, Catch[
    nmtd = num - t*D[den,x];
    {res,rr} = fastSubResultantPRS[den,nmtd,x];
    If[res===0,Throw[$Failed]];
    qq = SquareFree[res];
    qq = DeleteCases[qq,{f1_,f2_}/;Exponent[f1,t]==0];
    Total[
    Function[qi,
       If[Last[qi] == Exponent[den,x],
               s = den
             , (* else *)
               s = First[Cases[rr, y_ /; Exponent[y, x]==Last[qi]]];
               a = SquareFree[Coefficient[s,x,Exponent[s,x]]];
               s = Collect[Fold[ PolynomialQuotient[#1, PolynomialGCD[ First[#2], First[qi] ]^Last[#2], x ]&, s, a ], x, Together];
       ];
       Apply[ Plus,
         Function[qqi,
           RootSum @@ {
             Function @@ { qqi /. t-># },
             Function @@ { t*Log[s]/.t-># }
           } ] /@ Cases[ FactorList[First[qi]][[All, 1]], y_ /; Exponent[y,t] > 0 ]
       ]
    ] /@ qq ]
 ]];

Clear[IntegrateRationalFunction];

IntegrateRationalFunction[f_,x_]:=
(* Rational function integration 
   
   Given f in Q (x) returns its integral. *)
Module[{g, h, Q, R, num, den, P},
	DRPrint["Visit IntegrateRationalFunction"];
   	DRPrint["	Entries: f = ", f, ", variable = " ,x];
   	{num, den} = NumeratorDenominator[f];
   	{g, h} = HermiteReduce[num, den, x];	
	{Q, R} = PolyDivide[Numerator[h], Denominator[h], x];
   	If[ZeroPolynomialQ[R, x],
   		g + PolyInt[Q, x],
   		g + LazardRiobooTrager[R, Denominator[h], x]
   	]
]

LaurentSeries[a_,d_,F_,n_,x_]:=Module[{u,EE,h,B,G,CC,P,v,Q,Fs,H,sigma,j},
	If[deg[F,x] == 0, sigma = 0,
		sigma = 0;
		EE = d/F^n;
		h = a/(u[x]^n EE);
		{B,G} = fastExtendedEuclidean[EE,F,1,x];
		{CC,G} = fastExtendedEuclidean[D[F,x],F,1,x];
		j = -1;
		While[(j = j+1) <= n-1,
			P = u[x]^(n+j)EE^(j+1)h;
			v[j] = D[F,{x,j+1}]/(j+1);
			Q = Evaluate[P/.Table[D[u[x],{x,k}]->v[k],{k,0,j}]];
			h = D[h,x]/(j+1);
			Fs = PolynomialQuotient[F,PolynomialGCD[F,Q],x];
			If[deg[Fs,x] > 0,
				H=PolynomialMod[Q B^(j+1)CC^(n+j),Fs];
				sigma = sigma + 
				       RootSum[
				       	Function[Evaluate[Fs/.x->#]],
				       	Function[Evaluate[(H/.x->#)/(x-#)^(n-j)]]
				       ]
			];
		];
	];
	sigma
]		

FullPartialFraction[f_,x_]:=Module[{d,Q,R,DD,m},
	d = Denominator[f];
	{Q,R} = PolyDivide[Numerator[f],d,x];
	DD = Squarefree[d,x];
	m = Length[DD];
	Q + Total[Table[LaurentSeries[R,d,DD[[i]],i,x],{i,1,m}]]
]
 
LogToAtan[A_,B_,x_]:=Module[{d,c,g,a,b},
	{a,b}={A,B};
	If[Last[PolyDivide[a,b,x]]===0,
		2ArcTan[a/b],
		If[deg[a,x]<deg[b,x],
			LogToAtan[-b,a,x],
			{d,c,g}=ExtendedEuclideanFinal[b,-a,x];
			2ArcTan[PolynomialQuotient[(a d + b c),g,x]]+LogToAtan[d,c,x]
		]
	]
] 
 
(*
HO[A_,d_,x_]:=
(* Horowitz-Ostrogradsky Algorithm
    
   Given A,D in Q[x] with deg (A)< deg (D), D nonzero and
   coprime with A, return g,h in Q (x) such that A/D-dg/dx+h
   and h has a squarefree denominator. *) 
   Module[{Dm,Ds,n,m,B,CC,H,c,b,matrix,zerovec,vec1,vec2,vec3,sol,mycount},
   	If[deg[A,x]<deg[d,x], 
   	  Dm = PolynomialGCD[d,D[d,x]];
   	  Ds = PolynomialQuotient[d,Dm,x];
   	  n = deg[Dm,x]-1;
   	  m = deg[Ds,x]-1;
   	  B = Sum[b[i]x^i,{i,0,n}];
   	  CC = Sum[c[j]x^j,{j,0,m}];
   	  H = A - D[B,x]Ds + PolynomialQuotient[B Ds D[Dm,x],Dm,x] - CC Dm;
   	  vec1 = CoefficientList[H,x];
   	  zerovec = Table[0,{v,0,deg[d,x]-1}];
   	  vec2 = Union[Table[b[i],{i,0,n}],Table[c[i],{i,0,m}]];
   	  sol=Solve[vec1==zerovec,vec2];
   	  mycount=0;
   	  While[mycount <= m+n+1,
   	  	If[mycount <= n,
   			b[mycount]=sol[[1]][[mycount+1]][[2]],
   		  	c[mycount-n-1]=sol[[1]][[mycount+1]][[2]]
   		  ];
   		mycount=mycount+1
   	  ];
     {B/Dm,Cancel[CC/Ds]},
     Print["Error, Deg(",A, ") IS NOT  less than Deg(",d,")."]
   	]
  ]
    
HO[R_,x_]:=
(* Final version of Horowitz-Ostrogradsky Algorithm *)
HO[Numerator[R],Denominator[R],x]

slowIntRationalLogPart[A_,d_,x_]:=
(* Lazard - Rioboo - Trager algorithm. 
   
   Given A,d in Q[x] with deg (A)<deg (d), d nonzero, squarefree and coprime
   with A, return Integrate[A/d,x] *)
   Module[{a,j,Res,R,m,i,ii,t,Q,list,n,S,AA,q,sol,sum,L,theS},
   	list = SubResultant[d,A- t D[d,x],x];
   	Res = list[[1]];
   	R = list[[2]];
   	Q = First/@SquareFree[Res];
   	n = Length[Q];
   	i = 0;
   	While[(i = i + 1) <= n,
   		If[deg[Q[[i]],t] > 0,
   			If[i == deg[d,x],
   				S[i] = d,
   				S[i] = Cases[R,y_ /; deg[y,x]==i][[1]];
   				AA = SquareFree[lc[S[i],x]];
   				(*q = Length[AA];
   				j = 0;
   				While[(j = j + 1) <= q,
   					S[i] = PolynomialQuotient[S[i],PolynomialGCD[AA[[j]],Q[[i]]^j],t]
   				]*)
   				S[i] = 
   				Fold[PolynomialQuotient[#1,PolynomialGCD[First[#2],Q[[i]]^Last[#2]],t]&, 
   					   					 S[i], AA];
   			]
   		    (*S[i] = 1;*)
   		]
   		(*
   	While[(i = i + 1) <= n,
   		If[deg[ss[[i]],z] > 0,
   			If[i == deg[d,t],
   				S[i] = d,
   				S[i] = Cases[R,y_ /; deg[y,t]==i][[1]];
   				AA = First/@SquareFree[lc[S[i],t]];
   				S[i] = 
   				Fold[PolynomialQuotient[#1,PolynomialGCD[#2,ss[[i]]]^deg[#2,t],t]&, 
   					 S[i], AA];
   			](*,
   		    S[i] = 1;*)
   		]
   	];
   	*)
   	];
   	Function[{Q,S},
   		Table[
   		RootSum[ 
   			Function[Evaluate[Q1/.t->#]] , 
   			Function[Evaluate[# Log[S/.t->#]]]
   		] , {Q1, First /@ DeleteCases[FactorList[Q],u_/;FreeQ[u,t]] }]//Total
   	] @@@ Thread[{Q,Array[S,n]}] // Total
   ]	
   

IntRationalLogPart[A_,d_,x_]:=
(* Lazard - Rioboo - Trager algorithm. 
   
   Given A,d in Q[x] with deg (A)<deg (d), d nonzero, squarefree and coprime
   with A, return Integrate[A/d,x] *)
   Module[{a,j,Res,R,m,i,ii,t,Q,list,n,S,AA,q,sol,sum,L,theS},
   	list = fastSubResultantPRS[d, A - t D[d, x], x]; 
   	Res = First[list];
   	R = Last[list]; 
   	Q = First/@SquareFree[Res];
   	n = Length[Q];
   	i = 0;
   	While[(i = i + 1) <= n,
   		If[deg[Q[[i]],t] > 0,
   			If[i == deg[d,x],
   				S[i] = d,
   				S[i] = Cases[R,y_ /; deg[y,x]==i][[1]];
   				AA = SquareFree[lc[S[i],x]];
   				(*q = Length[AA];
   				j = 0;
   				While[(j = j + 1) <= q,
   					S[i] = PolynomialQuotient[S[i],PolynomialGCD[AA[[j]],Q[[i]]^j],t]
   				]*)
   				S[i] = 
   				Fold[PolynomialQuotient[#1,PolynomialGCD[First[#2],Q[[i]]^Last[#2]],t]&, 
   					   					 S[i], AA];
   			]
   		    (*S[i] = 1;*)
   		]
   	];
   	Function[{Q,S},
   		Table[
   		RootSum[ 
   			Function[Evaluate[Q1/.t->#]] , 
   			Function[Evaluate[# Log[S/.t->#]]]
   		] , {Q1, First /@ DeleteCases[FactorList[Q],u_/;FreeQ[u,t]] }]//Total
   	] @@@ Thread[{Q,Array[S,n]}] // Total
   ]	
*)
