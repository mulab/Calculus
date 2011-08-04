(* Integration of Elementary Function, algorithms from book Symbolic Integration, by M. Bronstein 
   CHAPTERS 3,4, and 5
   
   Authors: Luis A. Medina and Sasha Pavlyk
   
   Mathematica Version: 6.1
   
   *)

(* =========================== Chapter 3 =========================== *)
SplitFactor[p_, lv_List,ld_List] := Module[{S, theT},
  theT = Last[lv];
  S = PolynomialQuotient[
  	   PolynomialGCD[p, Derivation[lv, ld][p] ],
  	   PolynomialGCD[p, D[p, theT]], theT];
  If[Exponent[S, theT]==0,
  	{p, 1},
  (*Else*)
  	{1, S}*SplitFactor[ PolynomialQuotient[p, S, theT], lv, ld ]
  ]
] 

SplitSquarefreeFactor[0,lv_List,ld_List]:={ {{0, 1}},{{1, 1}} };
SplitSquarefreeFactor[p_,lv_List,ld_List]:=Module[{P,S,NN,theT,DP,degs,list},
	theT = Last[lv];
	list = SquareFreePositiveDegrees[p];
	degs =  Last /@ list;
	P = First /@ list;
	DP = Derivation[lv, ld][P];
	S = MapThread[ PolynomialGCD[#1, #2]&, {P, DP}];
	NN = MapThread[ PolynomialQuotient[#1,#2, theT]&, {P, S}];
	NN = Collect[NN, theT, Together];
	Thread/@ { {NN, degs}, {S, degs} }
]

CanonicalRepresentation[f_,lv_List,ld_List]:=Module[{a, d, q, r, dn, ds, b, c, theT},
	{a, d} = NumeratorDenominator[f];
	theT = Last[lv];
	{q, r} = PolyDivide[a, d, theT];
	{dn, ds} = SplitFactor[d, lv, ld];
	{b, c} = fastExtendedEuclidean[dn, ds, r, theT];
	{q, b/ds, c/dn}
]
(*========================== End of Ch 3 ===================================*)

(*=========================== Chapter 4 ====================================*)
SetAttributes[OrderNu, Listable];
OrderNu[p_, f_, t_] /; PolynomialQ[p, t] && Exponent[p,t] > 0 := Catch[Module[{ff, q, r, n=0},
	If[ PolynomialQ[f, t], 
		ff = DeleteCases[FactorSquareFreeList[f], {x_, k_}/; FreeQ[x, t], {1}];
		Throw[
			Total[Cases[ff, {x_, k_} /; ZeroPolynomialQ[PolynomialRemainder[x, p, t], t] :> k, {1}]]
		]
	];
	If[ RationalFunctionQ[f, t], 
		ff = NumeratorDenominator[f];
		ff = OrderNu[p, #, t]& /@ ff;
		If[ FreeQ[ff, $Failed], Throw[Subtract @@ ff]];
	];
	$Failed
]]

OrderNu[ Infinity, f_, t_] := {-1,1}.Exponent[NumeratorDenominator[f], t]
	
OrderNu[___] := $Failed

Remainder[f_,a_,x_]:=Module[{b, c, q, r, num, den},
	{num, den} = NumeratorDenominator[f];
	{b, c} = fastExtendedEuclidean[a, den, 1, x];
	{q, r} = PolyDivide[num c, a, x];
	r
]

ValueAtInfinity[f_, x_]/;RationalFunctionQ[f, x]:=Module[{a, b},
	{a, b} = NumeratorDenominator[f];
	If[ZeroPolynomialQ[a, x],
		0,
	(*Else*)
		If[Exponent[b, x] > Exponent[a, x],
			0,
		(*Else*)
			lc[a, x]/lc[b, x]
		]
	]
]

residue[f_,a_,lv_List,ld_List]:=Module[{theT,theF},
(* Possible error:  a has to be NORMAL *)
	theT = mainVar[a,lv];
	Remainder[Cancel[f*(a/Derivation[lv,ld][a])],a,theT]
]
(*========================== End of Ch 4=====================================*)

(*=========================== Chapter 5 =====================================*)


Clear[MonomialHermiteReduce];
(* Mack version with O(n) complexity. *)
MonomialHermiteReduce[f_,lv_List,ld_List]:=
Module[{ff, a, d, dm, cont=1, ds, dms, dm2, g, b, c, q, r, DD, theT},
	ff = CanonicalRepresentation[f, lv, ld];
	{a, d} = NumeratorDenominator[Last[ff]];
	theT = Last[lv];
	DD = Derivation[lv, ld];
	g = 0;
	dm = PolynomialGCD[ d, DD[d] ];
	If[FreeQ[dm, theT],
		dm = 1
	];
	ds = d/dm;
	While[Exponent[dm, theT] > 0,
		dm2 = PolynomialGCD[ dm,  DD[dm] ];
		If[Exponent[dm2, theT] == 0,dm2 = 1];	
		dms = PolynomialQuotient[dm, dm2, theT];
		{b,c} = fastExtendedEuclidean[
			          PolynomialQuotient[-ds DD[dm], dm, theT], (* exact division *)
			          dms,a,theT];
		a = c - DD[b]PolynomialQuotient[ds, dms, theT]; (* exact division *)
		g = g + b/dm;
		dm = dm2
	];
	{q, r} = PolyDivide[a, ds, theT];
	{g, r/ds, q + Total[Most[ff]]}
]

(* Quartic version *)
QuarticHermiteReduce[f_,lv_List,ld_List]:=
Module[{ff, a, d,dd, dm, v, i,u, g, b,c, j, q, r, DD, theT},
	ff = CanonicalRepresentation[f, lv, ld];
	{a, d} = NumeratorDenominator[Last[ff]];
	theT = Last[lv];
	DD = Derivation[lv, ld];
	dd = SquareFree[d];
    g = 0;
    Scan[If[Exponent[First[#], theT]>0,
    	v = First[#];
    	i = Last[#];
    	u = PolynomialQuotient[d,v^i, theT];
    	j = i;
    	While[(j = j - 1) >= 1,
    		{b, c} = fastExtendedEuclidean[u DD[v], v, -a/j, theT];
    		g = g + b/v^j;
    		a = -j c - u DD[b];
    	];
    	d = u*v
    ]&, dd];
    {q, r} = PolyDivide[a, u*v, theT];
    {g, r/(u*v), q + Total[Most[ff]] } 
]
    
PolyReduce[p_, lv_List, ld_List]:= Catch[
Module[{delta, m, q0, lambda, q, r, theT, DD},
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{delta, lambda} = Through[ {Exponent, lc}[ Last[ld], theT ] ];
	If[delta <=1, Throw[ $Failed ] ];
	If[Exponent[p, theT] < delta, Throw[ {0, p} ] ];
	m = Exponent[p, theT] - delta + 1;
	q0 = lc[p, theT]/(m lambda) theT^m;
	{q,r} = PolyReduce[Collect[p - DD[q0], theT], lv, ld];
	{q0 + q, r}
  ]
]
    
ResidueReduce[f_,lv_List,ld_List]:=
Module[{a, d, res, prs, z, theT, nn, ss, s, q, DD, cont, result=0},
   	DD = Derivation[lv,ld];
   	{a, d} = NumeratorDenominator[f];
	theT = Last[lv];
	{cont,d} = PolyContentPP[d, theT];
   	a = PolynomialRemainder[a/cont, d, theT];
   	cont = DD[d];
   	If[Exponent[cont,theT] <= Exponent[d, theT],
   		{res, prs} = fastSubResultantPRS[d, a - z cont, theT],
   		{res, prs} = fastSubResultantPRS[a - z cont, d, theT]
   	];
   	{nn,ss} = SplitSquarefreeFactor[res, lv, ld];
   	
   	Scan[Function[q, Catch[
   		If[Last[q] == Exponent[d,theT],
   			s = d,
   		(*Else*)
   			s = Cases[ prs, y_ /; Exponent[y,theT] == Last[q] ];
   			If[ s === {}, Throw[1]];
   			s = First[s];
   			s = Fold[PolynomialQuotient[#1, PolynomialGCD[First[#2], First[q]^Last[#2]], z]&, s, 
   				  SquareFreePositiveDegrees[lc[ s,theT ]] ];
   		];
   		result += Function[{sss,S},
   		     Table[
   		       RootSum[ 
   				Function[Evaluate[ss1/.z->#]] , 
   				Function[Evaluate[# Log[S/.z->#]]]
   		      ] , {ss1, First /@ FactorList[sss] } ]//Total
   	    ][ First[q], s ];
   	]], DeleteCases[ss, {_,_Integer?Negative},{1} ] ];
   	
   	{result, Boole[FreeQ[Times@@(First/@nn),theT] && FreeQ[Times@@(First/@nn),z]] }
]

(* Primitive Case *)
IntegratePolynomial[p_,lv_List,ld_List]/;(PrimitiveMonomialQ[lv,ld] && ReduceElementQ[p, lv, ld]):=
Module[{m, beta, a, b, c, q0, q, theT, DD, toCheck},
	DRPrint["Visit IntegratePolynomial, primitive case."];
	DRPrint["	Entries: p = ", p, ", {lv, ld} = ", {lv, ld},"."];
	theT = Last[lv];
	DD = Derivation[lv, ld];
	If[FreeQ[p, theT],
		Return[ {0, 1} ]
	];
	toCheck = LimitedIntegrate[ lc[p, theT], {Last[ld]}, Most[lv], Most[ld]] ;
	(* Second entry in LimitedIntegrate is intended to be a List *)
	If[toCheck === NoSolution,
		DRPrint["Failure comming from IntegratePolynomial, primitive case.  Reason: Failure came from LimitedIntegrate."];
		Return[ {0, 0} ]
	];
	{b, {c}} = toCheck;
	m = Exponent[p, theT];
	q0 = c*theT^(m + 1)/(m + 1) + b*theT^m;
	{q, beta} = IntegratePolynomial[p - DD[q0]//Together, lv, ld];
	DRPrint["Exit IntegratePolynomial, primitive case."];
	{q + q0, beta}
]

(* HyperTangent Case *)
IntegratePolynomial[p_,lv_List,ld_List]/;(HyperTangentMonomialQ[lv, ld] && ReduceElementQ[ p, lv, ld ]):=
Module[{q, r, alpha, c, theT, DD},
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{q, r} = PolyReduce[p, lv, ld];	
	alpha = Last[ld]/(theT^2 + 1);
	c = Coefficient[r, theT, 1]/(2 alpha);
	{q, c}
]

(* HyperExponential case *)
IntegratePolynomial[p_, lv_List, ld_List]/;(HyperExponentialMonomialQ[lv, ld]&& ReduceElementQ[ p, lv, ld ]):=
Module[{q, beta, a, i, v, theT, quotient, LV, LD},
	DRPrint["Visit IntegratePolynomial, hyperexponential case."];
	DRPrint["	Entries: p = ", p, ", {lv, ld} = ", {lv, ld},"."];
	theT = Last[lv];
	{q, beta} = {0, 1};
	i = OrderNu[theT, p, theT];
	quotient = Last[ld]/theT //Together;
	{LV, LD} = Most /@ {lv, ld}; 	
	While[i <= -OrderNu[Infinity, p, theT],
		If[ i =!= 0,
			a = Coefficient[p, theT, i];
			v = RischDE[i*quotient, a, LV, LD]; (* <- Not yet implemented for hyperexponentials. *)
			If[v === NoSolution,
				DRPrint["Failure comming from IntegratePolynomial, hyperexponential case. Reason: Failure came from RischDE."];
				beta = 0,
			(*Else*)
				q = q + v*theT^i
			]
		];
		i = i + 1
	];
	DRPrint["Exit IntegratePolynomial, hyperexponential case."];
	{q, beta}
]

IntegrateNonLinearNoSpecial[f_,lv_List,ld_List]:=Module[{g1, g2, beta, h, r, q1, q2, DD, theT},
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{g1, h, r} = MonomialHermiteReduce[f, lv, ld];	
	{g2, beta} = ResidueReduce[h, lv, ld];
	If[ZeroPolynomialQ[beta, theT], Return[{g1 + g2,0}] ];
	{q1, q2} = PolyReduce[Together[h - DD[g2] + r], lv, ld];
	{q1, q2} = Collect[{q1,q2}, theT, Together];
	If[ FreeQ[q2, theT], beta = 1, beta = 0 ];
	{g1 + g2 + q1, beta}
]

IntegrateHypertangentReduced[p_, lv_, ld_]/;HyperTangentMonomialQ[lv, ld]:=
Module[{theT, DD, m, q, r, c, d, q0, b, beta, h, a, toCheck},
	theT = Last[lv];
	DD = Derivation[lv, ld];
	m = -OrderNu[theT^2 + 1, p, theT];
	If[ m <= 0,
		Return[{0,1}]
	];
	h = (theT^2 + 1)^m p;
	{q, r} = PolyDivide[h, theT^2 + 1, theT];
	a = Coefficient[r, theT];
	b = r - a theT;
	toCheck = CoupledDESystem[-1, 0, 2*m*PolynomialQuotient[Last[ld], theT^2 + 1, theT], a, b, lv, ld];
	If[ toCheck == NoSolution,
		Return[{0, 0}]
	];
	{c, d} = toCheck;
	q0 = (c theT + d)/((theT^2 + 1)^m) //Together;
	{q, beta} = IntegrateHypertangentReduced[p - DD[q0] // Together, lv, ld];
	{q + q0, beta}
]

(* Working well for primitive, but not for hyperexponential since it needs IntegratePolynomial. *)
IntegrateMonomial[f_, lv_List,ld_List]/;(PrimitiveMonomialQ[lv, ld] || HyperExponentialMonomialQ[lv, ld]):=
Module[{g1, h, r, g2, beta, q},
	DRPrint["Visit IntegrateMonomial."];
	DRPrint["	Entries: f = ,",f,", {lv, ld} =",{lv ld}];
	{g1, h, r} = MonomialHermiteReduce[f, lv, ld];
	{g2, beta} = ResidueReduce[h, lv, ld];
	If[beta === 0,
		Return[{g1 + g2, 0}]
	];
	{q, beta} = IntegratePolynomial[h - Derivation[lv, ld][g2] + r //Together, lv, ld];
	DRPrint["Exit IntegrateMonomial."];
	{g1 + g2 + q, beta}
]

IntegrateMonomial[f_, lv_List,ld_List]/;HyperTangentMonomialQ[lv, ld]:=
Module[{g1, h, r, c, g2, beta, q2, p, q1, theT},
	DRPrint["Visit IntegrateMonomial."];
	DRPrint["	Entries: f = ,",f,", {lv, ld} =",{lv ld}];
	{g1, h, r} = MonomialHermiteReduce[f, lv, ld];
	{g2, beta} = ResidueReduce[h, lv, ld];
	theT = Last[lv];
	If[beta === 0,
		Return[{g1 + g2, 0}]
	];
	p = h - Derivation[lv, ld][g2] + r //Together ;
	{q1, beta} = IntegrateHypertangentReduced[p, lv, ld];
	If[ beta == 0, Return[g1+ g2 + q1, 0] ];  
	{q2, c} = IntegratePolynomial[p - Derivation[lv, ld][q1] //Together, lv, ld];
	If[ ZeroPolynomialQ[Derivation[lv, ld][c], theT ],
		Return[{g1 + g2 + q1 + q2 + c Log[theT^2 + 1], 1}]
	];
	DRPrint["Exit IntegrateMonomial."];
	{g1 + g2 + q1 + q2, 0}
]
Clear[IntegrateTranscendentalMonomial];

IntegrateTranscendentalMonomial[f_, lv_List, ld_List]/;(Length[lv]==1 && ld== {1} && RationalFunctionQ[f, First[lv]] == True) := 
IntegrateRationalFunction[f, First[lv]]

IntegrateTranscendentalMonomial[0,{},{},q_]:=q;

(* The function to call when using this Integration algorithm. *)
IntegrateTranscendentalMonomial[f_, lv_List, ld_List,q_:0]/; With[{Dt = Last[ld], t = Last[lv]},
	RationalFunctionQ[f, lv]&& Length[lv] === Length[ld] && 
	(PrimitiveMonomialQ[lv, ld] && !First[DerivativeQ[Dt, Most[lv], Most[ld] ] ] || 
 	(HyperExponentialMonomialQ[lv, ld] || HyperTangentMonomialQ[lv, ld]) && !First[RadicalLogarithmicDerivativeQ[Dt/t, Most[lv], Most[ld]] ])]:= 
Module[{ff, g, beta, theT, DD, q1},
	theT = Last[lv];
	DD = Derivation[lv, ld];
	ff = f;
	{g, beta} = IntegrateMonomial[ff, lv, ld];
	If[beta == 0,
		DRPrint["FAILURE.  Reason: Failure came from IntegrateMonomial."];
		Return[NoSolution]
	];
	q1 = q + g;
	ff = ff - DD[g] // Together;
	{beta, g} = DerivativeQ[ff, lv, ld];
	If[beta,
		Return[q1 + g],
		IntegrateTranscendentalMonomial[ff, Most[lv], Most[ld], q1]
	]
]

IntegrateTranscendentalMonomial[0,{},{}]:=0;

theIndeces[list1_, list2_] := 
 Last /@ SortBy[list1, First[otherF[list2, #]] &] // Quiet

RischIntegration[f_, x_] := 
 Module[{vars, ders, ts, tower, theF, t, indeces, int},
  theF = Together[TrigToTan[f]];
  tower = candidateTower[theF, x, t];
  theF = First[tower];
  vars = tower[[2]];
  ts = Rest[tower[[3]]];
  ders = Rest[tower[[4]]];
  indeces = theIndeces[ts, ders];
  vars = Part[vars, indeces];
  ders = Part[ders, indeces];
  ts = Part[ts, indeces];
  int = IntegrateTranscendentalMonomial[theF, Flatten[{x, ts}], 
    Flatten[{1, ders}]];
  TanToTrig[(int /. Thread[ts -> vars])] //. tan[y_] -> Tan[y]
  ]