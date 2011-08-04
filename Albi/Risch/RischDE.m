(* Integration of Elementary Function, algorithms from book 
   Symbolic Integration, by M. Bronstein 
   CHAPTER 6
   
   Authors: Luis A. Medina and Sasha Pavlyk
   
   Mathematica Version: 6.1
   
   Goal: This section is intended to solve the following equation
         
         	Dy + fy = g ,
         
         for given f and g and over a simple monomial extension of a differential field k.
   
 *)
 
WeakNormalizer[f_,lv_List,ld_List]:= 
Module[{dn, ds, g, d1, a, b, r, n, DD, theT, num, den, DS, list, z},
(* f in k(t) is weakly normalized with respect to t if residue_p(f) is not a
   positive integer for any normal irreducible p in k[t] such that f in R_p.
   This method return q in k[t] such that f-DD[q]/q is weakly normalized. *)	
	{num, den} = NumeratorDenominator[f];
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{dn,ds}= SplitFactor[den, lv, ld];   	   	   
	g = PolynomialGCD[ dn, D[dn, theT] ];
	DS = PolynomialQuotient[ dn, g, theT ];
	d1 = PolynomialQuotient[ DS, g, theT ];
	{a, b} = fastExtendedEuclidean[ PolynomialQuotient[den, d1, theT], d1, num, theT ];
	r = Resultant[ a - z DD[d1], d1, theT ];
	list = Select[ First /@ FactorList[r], Exponent[#, z] == 1 &];
 	If[list === {},Return[1]];
	list = (z/.ToRules[Roots[# == 0, z]])& /@ list;
	n = Select[Select[list, IntegerQ], Positive];
    Times @@ (Map[PolynomialGCD[ a - #1*DD[d1], d1] &, n]^n)
]

RdeNormalDenominator[f_,g_,lv_List,ld_List]:=Module[{dn, ds, en, es, p, h, theT, DD},
(* Given a derivation DD on k[t] and f, g in k[t] with f weakly normalized
   with respect to t, return either "no solution", in wich case the equation
   DD[y]+f*y = g [(1)] has no solution in k(t), or the quadruplet {a,b,c,h} such 
   that a, h in k[t], b,c in k<t>, and for any solution y in k(t) of (1), q=yh 
   in k<t> satisfies a*DD[q]+b*q = c. *)
	DRPrint["Visit RdeNormalDenominator."];
	DRPrint["	Entries: f = ", f, ", g = ", g, ", {lv, ld} = ", {lv, ld}, "."];
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{dn,ds} = SplitFactor[ Denominator[f //Together], lv, ld ];
	{en,es} = SplitFactor[ Denominator[g //Together], lv, ld ];
	p = PolynomialGCD[ dn, en ];
	h = PolynomialQuotient[ PolynomialGCD[ en, D[en,theT] ], 
		                    PolynomialGCD[p , D[p,theT] ], theT ];
	If[NonZeroPolynomialQ[ PolynomialRemainder[dn*h^2, en, theT], theT ],
		DRPrint["Failure comming from RdeNormalDenominator."];
		Return[NoSolution]
	];
	DRPrint["Exit RdeNormalDenominator."];
	{dn*h, dn*h*f - dn*DD[h], dn*h^2*g, h}
]

(* Primitive case *)
RdeSpecialDenominator[a_, b_, c_, lv_List, ld_List ] /; PrimitiveMonomialQ[lv, ld]  := {a, b, c, 1};

(* HyperExponential case *)
RdeSpecialDenominator[a_, b_, c_, lv_List, ld_List ] /; HyperExponentialMonomialQ[lv, ld]  := 
Module[{nb, nc, n, t = Last[lv], alpha, z, m, list, n1},
	(* Given a derivation DD on k[t], and a in k[t] and b,c in k<t> such that a != 0, 
	   return the quadruplet (as, bs, cs, h) such that all are in k[t] and r = q*h is in k[t] and 
	   r satisfied as*DD(r) + bs*r == cs *)
	DRPrint["Visit RdeSpecialDenominator, hyperexponential case."];
	DRPrint["	Entries: a = ", a, ", b = ", b, ", c = ", c, ", {lv, ld} = ", {lv, ld}, "."];  
	{nb, nc} = OrderNu[t, {b, c}, t];
	n = Min[ 0, nc - Min[0, nb] ];
	If[ nb == 0,
		alpha = Remainder[ -b/a, t, t];
		list = ParametricLogarithmicDerivative[ alpha, t, Last[ld], Most[lv], Most[ld] ];
		If[First[list] =!= NoSolution,
			{n1, m, z} = list; (* n1 & m are always integers  *)
			If[n1 === 1,
				n = Min[n, m]
			],
		(*else*)
		    If[Last[list] === 0,
		    	DRPrint["Failure comming from heuristic method."];
		    	Return[ $Failed ]
		    ]
		]
	];
	nb = With[{nn = Max[ 0, -nb, n-nc ], p = t}, 
		{a*p^nn, (b + n*a Last[ld]/t)p^nn, c*p^(nn-n), p^(-n)} // Together
	];
	DRPrint["Exit RdeSpecialDenominator, hyperexponential case."];
	DRPrint["	Output: ", nb]; 
	(*With[{nn = Max[ 0, -nb, n-nc ], p = t}, 
		{a*p^nn, (b + n*a Last[ld]/t)p^nn, c*p^(nn-n), p^(-n)} // Together
	]*)
	nb
] /; With[{t = Last[lv]}, NonZeroPolynomialQ[a, t] && NonZeroPolynomialQ[ PolynomialRemainder[a, t, t], t] ]

(* HyperTangent case *)
RdeSpecialDenominator[a_, b_, c_, lv_List, ld_List ] /; HyperTangentMonomialQ[lv, ld] && FreeQ[ld, Complex] := 
Module[{p, t = Last[lv], ht = Last[ld], nb, nc, n, n1, alpha, beta, m, eta, z, toCheck, theta},
	DRPrint["Visit RdeSpecialDenominator, hypertangent case."];
	DRPrint["	Entries: a = ", a, ", b = ", b, ", c = ", c, ", {lv, ld} = ", {lv, ld}, "."];   
	p = t^2 + 1;
	{nb, nc} = OrderNu[p, {b, c}, t];
	n = Min[0, nc - Min[0, nb] ];
	If[ nb == 0, 
		With[{tmp = Remainder[ -b/a, p, t]},
			{beta, alpha} = Coefficient[tmp, t, {0,1}];
			(* k[t]/(t^2+1) ~ k(I) *)
		];
		eta = PolynomialQuotient[ht, p, t];
		If[ First[LogarithmicDerivativeQ[2*beta, Most[lv], Most[ld]]],
			toCheck = ParametricLogarithmicDerivative[ alpha*I + beta, theta, (2 I eta) theta, Most[lv], Most[ld]];
			(* The ParametricLogarithmicDerivative that we have, requires the second entry to be HyperExponential and the third to be
			   its derivative.  That is the reason of the extra variable 'theta'.  *)
			If[First[toCheck] =!= NoSolution, 
				{n1, m, z} = toCheck;
				If[n1 === 1,
					n = Min[n, m]
				]
			]
		];
	];
	nb = With[{nn = Max[ 0, -nb, n-nc ]}, 
		{a*p^nn, b*p^nn + n*a*p^nn*Last[ld]/Last[lv], c*p^(nn-n), p^(-n)} // Together
	];
	DRPrint["Exit RdeSpecialDenominator, hypertangent case."];
	nb	
]

(* =============== BOUNDS ON DEGREE OF POLYNOMIAL SOLUTION ===================*)

(* Base Case: D = d/dt*)
RdeBoundDegree[a_, b_, c_, lv_List, ld_List]/;With[{t = Last[lv],dt = Last[ld]},
	{ {t}, {dt} } === {lv, ld} && NonZeroPolynomialQ[a, t]
]:=Module[{da, db, dc, m, n, theT},
	DRPrint["Visit RdeBoundDegree case D = d/d", Last[lv],"."];
	DRPrint["	Entries: a = ", a ,", b = ", b , ", c = ", c, ", {lv, ld} = ", {lv, ld}, "."];	
	theT = Last[lv];
	{da, db, dc} = Exponent[{a, b, c}, theT];
	n = Max[ 0, dc - Max[db,da - 1] ];
	If[db == da - 1,
		m = -lc[b, theT]/lc[a, theT];
		If[IntegerQ[m],
			n = Max[ 0, m, dc - db ];
		]
	];
	n
]
(* Primitive Case *)
RdeBoundDegree[a_, b_, c_, lv_List, ld_List]/;(PrimitiveMonomialQ[lv, ld] && NonZeroPolynomialQ[a, Last[lv]]):=
Module[{da, db, dc, n, alpha, m, z, beta, w, theT, toCheck, conditional,DD},
	DRPrint["Visit RdeBoundDegree primitive case."];
	DRPrint["	Entries: a = ", a ,", b = ", b , ", c = ", c, ", {lv, ld} = ", {lv, ld}, "."];
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{da, db, dc} = Exponent[{a, b, c}, theT];
	If[db > da,
		n = Max[0, dc - db],
	(* Else *)
		n = Max[0, dc - da + 1]
	];
	If[db == da - 1,
		alpha = -lc[b, theT]/lc[a, theT];
		toCheck = LimitedIntegrate[alpha, {Last[ld]}, Most[lv], Most[ld] ];
		If[toCheck =!= NoSolution && FreeQ[ First[toCheck], theT ] && IntegerQ[ First[ Last[toCheck] ] ],
			n = Max[ n, First[ Last[toCheck] ] ]
		];
	];
	If[db == da,
		alpha = -lc[b, theT]/lc[a, theT];
		{conditional, z} = LogarithmicDerivativeQ[ alpha, Most[lv], Most[ld] ];
		If[conditional,
			beta = -lc[a*DD[z] + b*z, theT]/(z*lc[a, theT]);
			toCheck = LimitedIntegrate[ beta, {Last[ld]}, Most[lv], Most[ld] ];
			If[toCheck =!= NoSolution && FreeQ[ First[toCheck], theT ] && IntegerQ[ First[ Last[toCheck] ] ],
			n = Max[ n, First[ Last[toCheck] ] ]
			]
		]
	];
	n
] 

(* HyperExponential Case *)
RdeBoundDegree[a_, b_, c_, lv_List, ld_List]/;HyperExponentialMonomialQ[lv, ld] && NonZeroPolynomialQ[a, Last[lv] ]:=
Module[{da, db, dc, n, alpha, z, n1, m, list, theT = Last[lv]},
	DRPrint["Visit RdeBoundDegree hyperexponential case."];
	DRPrint["	Entries: a = ", a ,", b = ", b , ", c = ", c, ", {lv, ld} = ", {lv, ld}, "."];
	{da, db, dc} = Exponent[{a, b, c}, theT];
	n = Max[0, dc - Max[db, da] ];
	If[da === db,
		alpha = -lc[b, theT]/lc[a, theT];
		list = ParametricLogarithmicDerivative[ alpha, theT, Last[ld], Most[lv], Most[ld] ]; (* Heuristic *)
		If[First[list] =!= NoSolution,
			{n1, m, z} = list; (* n1 & m are always integers  *)
			If[n1 === 1,
				n = Max[m, n]
			],
		(*Else*)
			If[Last[list] === 0,  (* <- this means ParametricLogarithmicDerivative failed, so put my own bound *)
				n = Max[n, 5];
			]
		]
	];
	n	
]

(* Non-Linear Case: deg(Dt)>1 *)
RdeBoundDegree[a_, b_, c_, lv_List, ld_List]/;With[{t = Last[lv],dt = Last[ld]},
	NonZeroPolynomialQ[a, t] && Exponent[dt,t] > 1 ]:=
Module[{da, db, dc, delta, lambda, n, m, DD, theT, Dt},
	DRPrint["Visit RdeBoundDegree case deg(Dt)>1."];
	DRPrint["	Entries: a = ", a ,", b = ", b , ", c = ", c, ", {lv, ld} = ", {lv, ld}, "."];
	theT = Last[lv];
	Dt = Last[ld];
	DD = Derivation[lv, ld];
	{da, db, dc} = Exponent[{a, b, c}, theT];
	{delta, lambda} = { Exponent[Dt, theT], lc[Dt, theT] };
	n = Max[ 0,dc - Max[ da + delta - 1, db ] ];
	If[db == da + delta -1,
		m = -lc[b,theT]/(lambda lc[a, theT]);
		If[ IntegerQ[m],
			n = Max[ 0, m, dc - db ];
		]
	];
	n
]
(* ==============END OF BOUNDS ON DEGREE OF POLYNOMIAL SOLUTION =============== *)

(* Special Polynomial Differential Equation *)
SPDE[a_,b_,c_,lv_List,ld_List,n_Integer]:=
Module[{g, toCheck, aa, bb, cc, r, z, bl, cl, m, alpha, beta, theT, DD},
(* Given a derivation DD on k[t], an integer n and a,b,c in k[t] with a!=0,
   return either "no solution", in which case the equation a*DD[q]+b*q=c has
   no solution of degree at most n in k[t], or a tuple {bl,cl,m, alpha, beta }
   such that bl,cl,alpha,beta in k[t], m in Z, and any solution q in k[t] of
   degree at most n of a DD[q] + b*q=c must be of the form q = alpha h + beta,
   where h in k[t], deg[h]<=m and DD[h]+ bl*h=cl. *)	
	DRPrint["Visit SPDE."];
	DRPrint["	Entries: a = ", a ,", b = ", b, ", c = ", c, ", {lv, ld} = ", {lv, ld}, "."];
	theT = Last[lv];
	DD = Derivation[lv,ld];
	If[n < 0,
		If[ZeroPolynomialQ[c, theT],
			Return[ {0, 0, 0, 0, 0} ]
			,
		(* Else *)
			DRPrint["Failure comming from SPDE, n < 0."];
			Return[NoSolution]
		]
	];
	g = PolynomialGCD[a , b];
	If[ FreeQ[g, theT], g = 1];
	If[ NonZeroPolynomialQ[ PolynomialRemainder[c, g, theT], theT],
		DRPrint["Failure comming from SPDE, gcd(a, b) doesn't divide c."];
		Return[NoSolution]
	];
	{aa, bb, cc} = Map[ PolynomialQuotient[ #1, g, theT ]&, {a, b, c} ];
	If[Exponent[aa, theT] == 0,
		DRPrint["Exit SPDE."];
		Return[{bb/aa, cc/aa, n, 1, 0}]
	];
	{r,z} = Collect[ fastExtendedEuclidean[bb, aa, cc, theT], theT, Together ];
	toCheck = SPDE[ aa, bb + DD[aa], Collect[ z - DD[r], theT ], lv, ld, n - Exponent[aa, theT] ];
	If[toCheck === NoSolution,
		Return[NoSolution]
	];
	{bl, cl, m, alpha, beta} = toCheck;
	DRPrint["Exit SPDE."];
	{bl, cl, m, aa*alpha, aa*beta + r}
]

(* Polynomial Risch DE: Non-cancellation case 1 *)
PolyRischDE[b_,c_,lv_List,ld_List,n:(_Integer|Infinity)]/;
With[{t = Last[lv], ht = Last[ld]}, 
  	NonZeroPolynomialQ[b, t] && ( {lv, ld} === { {t}, {1} } || Exponent[b, t] > Max[ 0, Exponent[ht, t] - 1 ] )
  	 ]:=
(* Given the derivation DD on k[t], n either an integer or Infinity, b,c in k[t] 
   with b!=0 and either DD=d/dt or deg[b,t]>Max[0,delta(t)-1], return either
   "no solution", in wich case the equation DD[q]+bq=c has no solution of degree
   at most n in k[t], or a solution q in k[t] of this equation with deg[q,t]<=n *)
Module[{q, m, p, nn, cc, DD, theT},
	DRPrint["Visit PolyRischDE non-cancellation case 1."];
	DRPrint[ "	Entries: b = ", b, ", c = ", c, ", {lv, ld} = ", {lv, ld}, ", n = ", n , "."];
	{nn, cc, q, DD} = {n, c, 0, Derivation[lv, ld]};
	theT = Last[lv];
	While[NonZeroPolynomialQ[cc, theT],
		m = Exponent[cc, theT] - Exponent[b, theT];
		If[ n < 0 || m < 0 || m > n,
			DRPrint["Failure comming from PolyRischDE, non-cancellation case 1."];
			Return[NoSolution];
		];
		p = lc[cc, theT]/lc[b, theT] theT^m;
		q = q + p;
		nn = m - 1;
		cc = cc - DD[p]- b p // Together;
	];
	DRPrint["Exit PolyRischDE, non-cancellation case 1."];
	q
] 

(* Polynomial Risch DE: Non-cancellation case 2 *)
PolyRischDE[b_,c_,lv_List,ld_List, n:(_Integer|Infinity) ]/;
With[{t = Last[lv], ht = Last[ld]}, With[{delta = Exponent[ht, t]},
  	Exponent[b, t] < delta-1 &&( {{t}, {1}} === {lv, ld} || delta >= 2 )
  	 ] ] :=
(* Given the derivation DD on k[t], n either an integer or Infinity, b,c in k[t] 
   with deg[b,t]<delta(t)-1 and either DD=d/dt or delta(t)>=2, return either
   "no solution", in which case the equation DD[q]+bq=c has no solution of degree
   at most n in k[t], or a solution q in k[t] of this equation with deg[q,t]<=n 
   or the tuple (h,b0,c0) such that h in k[t], b0,c0 in k, and for any solution
   q in k[t] of degree at most n of DD[q]+bq=c, y=q-h is a solution in k of 
   DD[y]+b0y =c0. *)
Module[{q, m, p, nn, cc, DD, theT, delta, lambda, h, b0, c0},
	DRPrint["Visit PolyRischDE non-cancellation case 2."];
	DRPrint[ "	Entries: b = ", b, ", c = ", c, ", {lv, ld} = ", {lv, ld}, ", n = ", n , "."];
	{nn, cc, q, DD} = {n, c, 0, Derivation[lv, ld]};
	theT = Last[lv];
	delta = Exponent[ Last[ld], theT ];
	lambda = lc[ Last[ld], theT ];
	While[NonZeroPolynomialQ[cc, theT],
		If[ nn == 0, m = 0, m = Exponent[cc, theT] - delta + 1 ];
		If[ nn < 0 || m <0 || m > nn, 
			DRPrint["Failure comming from PolyRischDE, non-cancellation case 2."];
			Return[NoSolution] 
		];
		If[ m > 0,
			p = lc[cc, theT]/(m lambda) theT^m,
		(*Else*)
			If[ Exponent[b, theT] != Exponent[cc, theT], Return[NoSolution] ];
			If[ Exponent[b, theT]==0, 
				{h, b0, c0} = {q, b, cc};
				Return[RischDE[b0, c0, Most[lv], Most[ld]] + h]
			];
			p = lc[cc, theT]/lc[b ,theT];
		];
		q = q + p;
		nn = m - 1;
		cc = Collect[ cc - DD[p] - b p, theT];
	];
	DRPrint["Exit PolyRischDE, non-cancellation case 2."];
	q
] 

(* Polynomial Risch DE: Non-cancellation case 3 *)
PolyRischDE[b_,c_,lv_List,ld_List,n:(_Integer|Infinity)]/;
With[{t = Last[lv], ht = Last[ld]}, With[{ delta = Exponent[ht,t]}, 
  	Exponent[b,t] == delta-1 && delta >= 2 ] ]:=
(* Given the derivation DD on k[t] with delta(t)>=2, n either an integer or 
   Infinity, b,c in k[t] with deg[b,t]=delta(t)-1 return either  "no solution", 
   in wich case the equation DD[q]+bq=c has no solution of degree at most n 
   in k[t], or a solution q in k[t] of this equation with deg[q,t]<=n 
   or the tuple (h,m,cl) such that h in k[t], m in Z, cl in k[t], and for any 
   solution q in k[t] of degree at most n of DD[q]+bq=c, y=q-h is a solution 
   in k of DD[y]+ b0 y = c0. *)
Module[{q, m, p, nn, cc, cl, DD, theT, delta, lambda, MM, u, h, ml},
	DRPrint["Visit PolyRischDE non-cancellation case 3."];
	DRPrint[ "	Entries: b = ", b, ", c = ", c, ", {lv, ld} = ", {lv, ld}, ", n = ", n , "."];	
	{nn, cc, q, DD} = {n, c, 0, Derivation[lv, ld]};
	theT = Last[lv];
	{delta, lambda} = Through[ {Exponent, lc}[ Last[ld], theT ] ];
	With[{ mc = Cancel[ -lc[b, theT]/lambda ] }, (* might be expensive, profiling will show *) 
	   MM = If[ IntegerQ[mc] && mc > 0, mc, -1]
	];
	While[NonZeroPolynomialQ[cc, theT],
		m = Max[ MM, Exponent[cc, theT]- delta + 1 ];
		If[ nn < 0 || m < 0 || m > nn, 
			Return[NoSolution] 
		];
		u = m lambda + lc[b, theT];
		If[ZeroPolynomialQ[u, theT], 
			{h, ml, cl} = {q, m, cc};
			Return[ PolyRischDE[b, cl, lv, ld, ml] + h ]
		];
		If[ m > 0, p = (lc[cc, theT]/u)*theT^m,
			If[Exponent[cc, theT] != delta - 1, 
				Return[NoSolution] 
			];
			p = lc[cc, theT]/lc[b, theT]
		];
		q = q + p;
		nn = m - 1;
		cc = Collect[cc - DD[p] - b p, theT]
	];
	DRPrint["Exit PolyRischDE, non-cancellation case 3."];
	q
]

(* Polynomial Risch DE cancelation case, the primitive case *)
PolyRischDE[b_,c_,lv_List,ld_List,n_]/; 
  PrimitiveMonomialQ[lv, ld] && NonZeroPolynomialQ[ b, Last[lv] ] && 
  FreeQ[ b, Last[lv] ] && PolynomialQ[c, Last[lv] ] :=
Module[{bb, cc, q, nn, m, s, theT, DD, z, conditional, p},
	DRPrint["Visit PolyRischDE cancellation, the primitive case."];
	DRPrint[ "	Entries: b = ", b, ", c = ", c, ", {lv, ld} = ", {lv, ld}, ", n = ", n , "."];	
	theT = Last[lv];
	DD = Derivation[lv,ld];
	{conditional, z} = LogarithmicDerivativeQ[ b, Most[lv], Most[ld] ];
	If[conditional,
		{conditional, p} = DerivativeQ[z*c, lv ,ld];
		If[conditional && PolynomialQ[p, theT] && (Exponent[p, theT] <= n),
			Return[p/z],
		(*Else*)
			DRPrint["Failure comming from PolyRischDE cancellation case, the primitive case. (1)"];
			Return[NoSolution]
		]
	];
	If[ZeroPolynomialQ[c, theT], 
		Return[0]
	];
	If[n < Exponent[c, theT],
		DRPrint["Failure comming from PolyRischDE cancellation case, the primitive case. (2)"];
		Return[NoSolution]
	];
	q = 0;
	{cc, nn} = {c, n};
	While[NonZeroPolynomialQ[cc, theT],
		m = Exponent[cc, theT];
		If[ nn < m,
			DRPrint["Failure comming from PolyRischDE cancellation case, the primitive case. (3)"];
			Return[NoSolution]
		];
		s = RischDE[b, lc[cc, theT], Most[lv], Most[ld] ];
		If[s === NoSolution,
			DRPrint["Failure comming from PolyRischDE cancellation case, the primitive case. (4)"];
			Return[NoSolution]
		];
		q = q + s*theT^m;
		nn = m - 1;
		cc = Collect[cc - b*s*theT^m - DD[s*theT^m], theT];
	];
	DRPrint["Exit PolyRischDE cancellation case, the primitive case."];
	q
]

(* Polynomial Risch DE cancelation case, the hyperexponential case *)
PolyRischDE[b_,c_,lv_List,ld_List,n_]/;
	HyperExponentialMonomialQ[lv, ld] && NonZeroPolynomialQ[b, Last[lv]] && 
	FreeQ[b, Last[lv]]&& PolynomialQ[c, Last[lv]]:=
Module[{z, m, n1, nn, cc, s, p, theT, toCheck, DD, conditional, q, quotient},
(* NOTE:  This method depends on ParametricLogarithmicDerivative which is heuristic, therefore it can fail even if
          there is a solution 
*)
	DRPrint["Visit PolyRischDE cancellation, the hyperexponential case."];
	DRPrint[ "	Entries: b = ", b, ", c = ", c, ", {lv, ld} = ", {lv, ld}, ", n = ", n , "."];	
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{cc, nn} = {c, n};
	quotient = Last[ld]/Last[lv] //Together;
	toCheck = ParametricLogarithmicDerivative[ b, theT, Last[ld], Most[lv], Most[ld] ]; (* Heuristic *)
	If[ First[toCheck] === NoSolution && Last[toCheck] == 0,
		DRPrint["Heuristic method failed."];
		Return[NoSoluiton]
	];
	If[ First[toCheck] =!= NoSolution,
		{n1, m, z} = toCheck; (* <- m & n1 are integers *)
		{conditional, p} = DerivativeQ[cc*z*theT^m, lv, ld];
		q = p/(z theT^m)//Together;
		If[ conditional && 	ReduceElement[p, lv, ld] && PolynomialQ[q, theT] && Exponent[q, theT] <= nn,
			Return[q],
		(*Else*)
			Return[NoSolution]
		]		
	];
	If[ZeroPolynomialQ[cc, theT],
		Return[0]
	];
	If[nn < Exponent[cc, theT],
		Return[NoSolution]
	];
	q = 0;
	While[NonZeroPolynomialQ[cc, theT],
		m = Exponent[cc, theT];
		If[ nn < m,
			Return[NoSolution]
		];
		s = RischDE[b + m quotient, lc[cc, theT], Most[lv], Most[ld] ];
		If[s === NoSolution,
			Return[NoSolution]
		];
		q = q + s* theT^m;
		nn = m - 1;
		cc = Collect[cc - b*s*theT^m - DD[s theT^m], theT];
	];
	DRPrint["Exit PolyRischDE cancellation case, the hyperexponential case."];
	q 
]

(* Polynomial Risch DE cancelation case, the hypertangent case *)
PolyRischDE[b_,c_,lv_List,ld_List,n_]/;
	HyperTangentMonomialQ[lv, ld]&& FreeQ[b, Last[lv]]&& PolynomialQ[c, Last[lv]]:=
Module[{z, m, n1, nn, ccl, c1, c0, cc, u, v, p, theT, toCheck, DD, h, q, eta, r},
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{nn, cc} = {n, c};
	If[nn == 0,
		If[ FreeQ[cc, theT],
			If[NonZeroPolynomialQ[b, theT],
				Return[RischDE[b, cc, Most[lv],Most[ld] ] ],
			(*Else If *)
				q = IntegratePolynomial[cc, Most[lv], Most[ld]];
				If[ FreeQ[q, theT],
					Return[q],
				(*Else*)
					Return[NoSolution]
				]
			],
		(*Else*)
			Return[NoSolution]
		]
	];
	p = theT^2 + 1;
	eta = Last[ld]/p //Together;
	{ccl, r} = PolyDivide[cc, p, theT];
	{c1, c0} = Coefficient[r, theT, {1, 0} ];
	(* next function need to be implemented *)
	toCheck = CoupledDESystem[-1, b, -nn eta, c0, c1, lv, ld];
	If[ toCheck === NoSolution,
		Return[ NoSolution ]
	];
	{u, v} = toCheck;
	If[ nn === 1,
		Return[u * theT + v]
	];
	r = u + v * theT;
	cc = PolynomialQuotient[(cc - DD[r] - (b - nn * eta)r), p, theT]; (* exact division *)
	h = PolyRischDE[b, cc, lv, ld, nn - 2];
	If[ h === NoSolution,
		Return[NoSolution]
	];
	DRPrint["Exit PolyRischDE cancellation case, the hypertangent case."];
	p * h + r;
]

PolyRischDE[0,c_,lv_List,ld_List,n_]/; PrimitiveMonomialQ[lv, ld] || HyperExponentialMonomial[lv, ld] || HyperTangentMonomial[lv, ld]:= 
Module[{beta,p},
	DRPrint["Visit PolyRischDE case primitive and b = 0."];
	DRPrint["	Entries: b = ", 0, ", c = ", c, ", {lv, ld} = ", {lv, ld},"."];
	{p, beta} = IntegratePolynomial[c, lv, ld];
	If[beta ===1,
		Return[p],
		Return[NoSolution]
	]
]

RischDE[f_,g_,lv_,ld_]/; PrimitiveMonomialQ[lv, ld] || HyperExponentialMonomialQ[lv, ld] || HyperTangentMonomialQ[lv, ld]:= 
Module[{q, ff, gg, toCheck, a, b, c, h1, h2, n, alpha, beta, sol, DD},
	DRPrint["Visit RischDE."];
	DRPrint["	Entries: f = ", f, ", g = ", g, ", {lv, ld} = ", {lv, ld},"."];
	DD = Derivation[lv,ld];
	q = WeakNormalizer[f, lv, ld];
	ff = f - DD[q]/q //Together;
	gg = q*g //Together;
	toCheck = RdeNormalDenominator[ff, gg, lv, ld];
	If[toCheck === NoSolution,
		DRPrint["Failure comming from RischDE.  Reason:  Failure came from RdeNormalDenominator."];
		Return[NoSolution]
	];
	{a, b, c, h1} = toCheck;
	toCheck = RdeSpecialDenominator[a, b, c, lv, ld];
	If[toCheck === $Failed,   
		DRPrint["Failure comming from RischDE.  Reason: Failure came from RdeSpecialDenominator."];					
		Return[NoSolution] (* This happend bacause ParametricLogarithmicDerivative is heuristic. *)    
	];
	{a, b, c, h2} = toCheck;
	toCheck = RdeBoundDegree[a, b, c, lv, ld];
	If[toCheck === $Failed,   (* <- Same reason as above.*)
		Return[NoSolution]
	];
	n = toCheck;
	toCheck = SPDE[a, b, c, lv, ld, n];
	If[toCheck === NoSolution,
		Return[NoSolution]
	];
	{b, c, n, alpha, beta} = toCheck;
	sol = PolyRischDE[b, c, lv, ld, n];
	If[sol === NoSolution,
		Return[NoSolution]
	];
	sol = alpha*sol + beta;
	sol = (sol/h2)/h1;
	DRPrint["Exit RischDE."];
	sol/q //Together
]

RischDE[___]:= NoSolution;