(* Integration of Elementary Function, algorithms from book 
   Symbolic Integration, by M. Bronstein 
   CHAPTER 8
   
   Authors: Luis A. Medina and Sasha Pavlyk
   
   Mathematica Version: 6.1
 *)
 
(* CoupledDE Cancellation case, primitive case. *)
CoupledDEPoly[a_,b1_,b2_,c1_,c2_,lv_List,ld_List,n_]/;PrimitiveMonomialQ[lv, ld]:=Module[{b, z, z1, z2, p1, p2, nn, cc1, cc2, q1, q2, m, s1, s2, theT, DD, toCheck},
 	DRPrint["Vist CoupledDEPoly, primitive case."];
 	DRPrint["	Entries: a = ", a, ", b1 = ", b1, ", b2 = ", b2, ", c1 = ", c1, ", c2 = ", c2, ", {lv, ld} = ", {lv, ld}, "."];
 	theT = Last[lv];
 	DD = Derivation[lv, ld];
 	toCheck = LogarithmicDerivativeQ[b, lv, ld];
 	If[ First[toCheck] === True &&  FreeQ[ Last[toCheck], theT ],
 		If[Sqrt[a] === I,
 			{z1, z2} = {myRe[toCheck], myIm[toCheck]}, 
 		(*Else*)
 			{z1, z2} = Coefficient[ Last[toCheck]/.Sqrt[a]-> z, z, {0, 1} ]
 		];
 		toCheck = DerivativeQ[z1 c1 + a z2 c2, lv, ld];
 		If[ First[toCheck] === False,
 			DRPrint["Failure comming from CoupledDEPoly. (1)"];
 			Return[NoSolution]
 		];
 		p1 = Last[toCheck];
 		If[!PolynomialQ[p1, theT],
 			DRPrint["Failure comming from CoupledDEPoly. (2)"];
 			Return[NoSolution]
 		];
 		If[ Exponent[p1, theT] > n,
 			DRPrint["Failure comming from CoupledDEPoly. (3)"];
 			Return[NoSolution]
 		];
 		toCheck = DerivativeQ[z2 c1 + z1 c2, lv, ld];
 		If[ First[toCheck] === False,
 			DRPrint["Failure comming from CoupledDEPoly. (4)"];
 			Return[NoSolution]
 		];
 		p2 = Last[toCheck];
 		If[ PolynomialQ[p2, theT] && Exponent[p2, theT] <= n,
 			DRPrint["Exit CoupledDEPoly, primitive case."];
 			Return[{(z1 p1 - a z2 p2)/(z1^2 - a z2^2), (z1 p2 - z2 p1)/(z1^2 - a z2^2)}],
 			DRPrint["Failure comming from CoupledDEPoly. (5)"];
 			Return[NoSolution]
 		]
 	];
 	If[ ZeroPolynomialQ[c1, theT] && ZeroPolynomialQ[c2, theT],
 		DRPrint["Exit CoupledDEPoly, primitive case."];
 		Return[{0, 0}]
 	];
 	If[ n < Max[ Exponent[c1, theT], Exponent[c2, theT] ],
 		DRPrint["Failure comming from CoupledDEPoly. (6)"];
 		Return[NoSolution]
 	];
 	{q1, q2} = {0, 0};
 	{cc1, cc2, nn} = {c1, c2, n};
 	While[NonZeroPolynomialQ[c1, theT] || NonZeroPolynomialQ[c2, theT],
 		m = Max[ Exponent[cc1, theT], Exponent[cc2, theT] ];
 		If[ nn < m,
 			DRPrint["Failure comming from CoupledDEPoly. (7)"];
 			Return[NoSolution]
 		];
 		toCheck = CoupledDESystem[ a, b1, b2, Coefficient[cc1, theT, m], Coefficient[cc2, theT, m], Most[lv], Most[ld] ];
 		If[ toCheck === NoSolution,
 			DRPrint["Failure comming from CoupledDEPoly. (8)"];
 			Return[NoSolution]
 		];
 		{s1, s2} = toCheck;
 		q1 = q1 + s1 theT^m;
 		q2 = q2 + s2 theT^m;
 		nn = m - 1;
 		cc1 = cc1 - DD[s1 theT^m, theT] - (b1 s1 + a b2 s2)theT^m //Together;
 		cc2 = cc2 - DD[s2 theT^m, theT] - (b2 s1 + b1 s2)theT^m //Together;
 	];
 	DRPrint["Exit CoupledDEPoly, primitive case."];
 	{q1, q2}
 ]
 
(* CoupledDE Cancellation case, hyperexponential case. *)
CoupledDEPoly[a_,b1_,b2_,c1_,c2_,lv_List,ld_List,n_]/;HyperExponentialMonomialQ[lv, ld]:=Module[{b, z, z1, z2, p1, p2, nn, cc1, cc2, q1, q2, m, s1, s2, theT, DD, toCheck},
	DRPrint["Vist CoupledDEPoly, hyperexponential case."];
 	DRPrint["	Entries: a = ", a, ", b1 = ", b1, ", b2 = ", b2, ", c1 = ", c1, ", c2 = ", c2, ", {lv, ld} = ", {lv, ld}, "."];
	theT = Last[lv];
	DD = Derivation[lv, ld];
	toCheck = ParametricLogarithmicDerivative[b1 + Sqrt[a]b2, theT, Last[ld], Most[lv], Most[ld] ];
	If[ First[toCheck] === 1 && FreeQ[ Last[toCheck], theT ],
		If[Sqrt[a] === I,
			{z1, z2} = {myRe[toCheck], myIm[toCheck]},
		(*Else*)
			{z1, z2} = Coefficient[ Last[toCheck]/.Sqrt[a]-> z, z, {0, 1} ]
		];
		m = toCheck[[2]];
 		toCheck = DerivativeQ[(z1 c1 + a z2 c2)theT^m, lv, ld];
 		If[ First[toCheck] === False,
 			DRPrint["Failure comming from CoupledDEPoly, hyperexponential case (1)."];
 			Return[NoSolution]
 		];
 		p1 = Last[toCheck];
 		If[!ReduceElementQ[p1, lv, ld],
 			DRPrint["Failure comming from CoupledDEPoly, hyperexponential case (2)."];
 			Return[NoSolution]
 		];
 		toCheck = DerivativeQ[(z2 c1 + z1 c2)theT^m, lv, ld];
 		If[ First[toCheck] === False,
 			DRPrint["Failure comming from CoupledDEPoly, hyperexponential case (3)."];
 			Return[NoSolution]
 		];
 		p2 = Last[toCheck];
 		If[ ReduceElementQ[p2, lv, ld],
 			{q1, q2} = {(z1 p1 - a z2 p2)theT^(-m)/(z1^2 - a z2^2), (z1 p2 - z2 p1)theT^(-m)/(z1^2 - a z2^2)};
 			If[PolynomialQ[q1, theT] && PolynomialQ[q2, theT] && Exponent[q1, theT] <= n && Exponent[q2, theT] <=n,
 				DRPrint["Exit CoupledDEPoly, hyperexponential case."];
 				Return[{q1, q2}],
 			(*Else*)
	 			DRPrint["Failure comming from CoupledDEPoly, hyperexponential case (4)."];
 				Return[NoSolution]
 			],
 		(*Else*)
 			DRPrint["Failure comming from CoupledDEPoly, hyperexponential case (5)."];
 			Return[NoSolution]
 		];
 		
 	];
	If[ ZeroPolynomialQ[c1, theT] && ZeroPolynomialQ[c2, theT],
		DRPrint["Exit CoupledDEPoly, hyperexponential case."];
 		Return[{0, 0}]
 	];
 	If[ n < Max[ Exponent[c1, theT], Exponent[c2, theT] ],
		DRPrint["Failure comming from CoupledDEPoly, hyperexponential case (6)."];
 		Return[NoSolution]
 	];
 	{q1, q2} = {0, 0};
 	{cc1, cc2, nn} = {c1, c2, n};
 	While[NonZeroPolynomialQ[cc1, theT] || NonZeroPolynomialQ[cc2, theT],
 		m = Max[ Exponent[cc1, theT], Exponent[cc2, theT] ];
 		If[ nn < m,
 			DRPrint["Failure comming from CoupledDEPoly, hyperexponential case (7)."];
 			Return[NoSolution]
 		];
 		toCheck = CoupledDESystem[ a, b1+ m PolynomialQuotient[Last[ld],theT,theT], b2, Coefficient[cc1, theT, m], Coefficient[cc2, theT, m], Most[lv], Most[ld] ];
 		If[ toCheck === NoSolution,
 			DRPrint["Failure comming from CoupledDEPoly, hyperexponential case (8)."];
 			Return[NoSolution]
 		];
 		{s1, s2} = toCheck;
 		q1 = q1 + s1 theT^m;
 		q2 = q2 + s2 theT^m;
 		nn = m - 1;
 		cc1 = cc1 - DD[s1 theT^m, theT] - (b1 s1 + a b2 s2)theT^m //Together;
 		cc2 = cc2 - DD[s2 theT^m, theT] - (b2 s1 + b1 s2)theT^m //Together
 	];
 	DRPrint["Exit CoupledDEPoly, hyperexponential case."];
 	{q1, q2}	
] 	

(* CoupledDE Cancellation case, hypertangent case. *)
CoupledDEPoly[a_,b1_,b2_,c1_,c2_,lv_,ld_,n_Integer]/;HyperTangentMonomialQ[lv, ld] && a==-1 :=
Module[{c, p, z1, z2, h1, h2, s1, s2, d1, d2, eta, theT, DD, toCheck},
	theT = Last[lv];
	DD = Derivation[lv, ld];
	If[ n == 0,
		If[ FreeQ[c1, theT] && FreeQ[c2, theT],
			Return[ CoupledDESystem[ b1, b2, c1, c2, Most[lv], Most[ld] ] ],
		(*Else*)
			Return[NoSolution]
		]
	];
	p = theT - I;
	eta = PolynomialQuotient[Last[lv], theT^2+1, theT]; (* exact division *)
	toCheck = (c1 + c2 I)/.theT -> I;
	{z1, z2} = {myRe[toCheck], myIm[toCheck]};
	toCheck = CoupledDESystem[ a, b1, b2 - n eta, z1, z2, Most[lv], Most[ld] ];
	If[ toCheck === NoSolution,
		Return[NoSolution]
	];
	{s1, s2} = toCheck;
	c = (c1 - z1 + n eta(s1 theT + s2) + (c2 - z2 + n eta(s2 theT - s1))I)/p //Together;
	{d1, d2} = {Re[c], Im[c]};
	toCheck = CoupledDECancel[b1, b2 + eta, d1, d2, lv, ld, n - 1];
	If[ toCheck === NoSolution,
		Return[NoSolution]
	];
	{h1, h2} = toCheck;
	{h1 theT + h2 + s1, h2 theT - h1 + s2}
]		

CoupledDESystem[a_,f1_,f2_,g1_,g2_, lv_List, ld_List]:= 
Module[{f, g,ff, gg, q, aa, b, c, h1, h2, n , toCheck, theT, DD, alpha, beta, delta, b1, b2, c1, c2, x, q1, q2},
	theT = Last[lv];
	DD = Derivation[lv, ld];
	delta = Exponent[ Last[ld], theT ];
	f = f1 + Sqrt[a]f2;
	g = g1 + Sqrt[a]g2;
	q = WeakNormalizer[f, lv, ld];
	ff = f - DD[q]/q //Together;
	gg = q*g //Together;
	toCheck = RdeNormalDenominator[ff, gg, lv, ld];
	If[ toCheck === NoSolution,
		DRPrint["Failure comming from CouledDESystem.  Reason:  Failure came from RdeNormalDenominator."];
		Return[NoSolution]
	];
	{aa, b, c, h1} = toCheck;
	toCheck = RdeSpecialDenominator[aa, b, c, lv, ld];
	If[ toCheck === $Failed,   
		DRPrint["Failure comming from RischDE.  Reason: Failure came from RdeSpecialDenominator."];					
		Return[NoSolution] (* This happend bacause ParametricLogarithmicDerivative is heuristic. *)    
	];
	{aa, b, c, h2} = toCheck;
	toCheck = RdeBoundDegree[aa, b, c, lv, ld];
	If[ toCheck === $Failed,   (* <- Same reason as above.*)
		Return[NoSolution]
	];
	n = toCheck;
	toCheck = SPDE[aa, b, c, lv, ld, n];
	If[ toCheck === NoSolution,
		Return[NoSolution]
	];
	{b, c, n, alpha, beta} = toCheck;
	If[ (delta <= 1 && FreeQ[b, theT] && ld =!= {1}) || (delta >= 2 && Exponent[b, theT] === delta - 1 && n === -lc[b, theT]/lc[ld, theT]),
		{b1, b2} = Coefficient[b/.Sqrt[a]->x, x,{0,1}];
		{c1, c2} = Coefficient[c/.Sqrt[a]->x, x,{0,1}];
		toCheck = {CoupledDEPoly[a, b1, b2, c1, c2, lv, ld, n],0},
	(*Else*)
		toCheck = {PolyRischDE[b, c, lv, ld, n],1}//Together
	];
	If[ First[toCheck] === NoSolution,
		Return[NoSolution]
	];
	If[ Last[toCheck] === 1, (* it is comming from PolyRischDE *)
		If[Sqrt[a] === I,
			{q1, q2} = {myRe[First[toCheck]],myIm[First[toCheck]]},
		(*Else*)
			{q1, q2} = Coefficient[First[toCheck]/.Sqrt[a]-> x, x,{0,1}];
		],
	(*Else*)
		{q1, q2} = First[toCheck];
	];
	{q1, q2} = alpha*{q1, q2} + beta;
	{q1, q2} = ({q1, q2}/h2)/h1;
	{q1, q2}/q //Together
]
	