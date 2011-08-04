(* Integration of Elementary Function, algorithms from book Symbolic Integration, by M. Bronstein 
   CHAPTER 7
   
   Authors: Luis A. Medina and Sasha Pavlyk
   
   Mathematica Version: 6.1
   
   Goal: This section is intended to solve the following equation
         
         	Dy + fy = c1*g1 + .. + cm*gm ,
         
         for given f and g1,...,gm over a simple monomial extension of a differential field k and ci in Const(k(t)).  
 *)

ParamRdeNormalDenominator[f_,g_List,lv_List,ld_List]:=
Module[{dn, ds, en, es, p, h, theT, DD},
(* Given a derivation DD on k[t] and f, g1,..,gm in k(t) with f weakly normalized
   with respect to t, return the tuple {a,b,G1,..,Gm,h} such that a, h in k[t], 
   b in k<t>, G1,..,Gm in k(t), and for any solution c1,..,cm in Const(k) and 
   y in k(t) of DD[y]+f*y = Sum[ci*gi,{i,m}], q=y*h in k<t> satisfies 
   a*DD[q]+b*q = Sum[ci*Gi,{i,m}]. *)
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{dn,ds} = SplitFactor[ Denominator[f], lv, ld ];
	{en,es} = SplitFactor[ PolynomialLCM @@ Denominator[ Together[g] ], lv, ld ];
	p = PolynomialGCD[dn, en];
	h = PolynomialQuotient[ PolynomialGCD[en, D[en, theT] ],
				PolynomialGCD[p, D[p, theT] ], theT];
	
	{ dn*h, dn*h*f - dn*DD[h], dn*h^2*g, h }
]   

(* Primitive Case *)
ParamRdeSpecialDenominator[a_, b_, g_List, lv_List, ld_List]/;PrimitiveMonomialQ[lv ,ld]:={a, b, g, 1};

(* HyperExponential Case *)
ParamRdeSpecialDenominator[a_, b_, g_List, lv_List, ld_List]/;HyperExponentialMonomialQ[lv ,ld]:=
Module[{nb, nc, p, n, alpha, NN, theT, toCheck, s, m, z},
	theT = Last[lv];
	nb = OrderNu[theT, b, theT];
	nc = OrderNu[theT, g, theT]; 
	n = Min[ 0, nc - Min[0, nb] ];
	If[nb === 0,
		alpha = Remainder[-b/a, theT, theT];
		toCheck = ParametricLogarithmicDerivative[ alpha, theT, Last[ld], Most[lv], Most[ld] ];
		(* At this point, ParametricLogarithmicDerivative is heuristic *)
		If[First[toCheck] =!= $Failed,
			{m, s, z} = toCheck; (* <- s, m are always integers *)
			If[m === 1,
				n = Min[n ,s]
			],
		(* Else *)
		    If[Last[toCheck] === 0,(* <- this is because it is heuristic *)
		    	DRPrint["Failure comming from ParamRdeSpecialDenominator.  Reason: Hueristic method failed."];
		    	Return[$Failed];
		    ]
		]
	];
	NN = Max[0, -nb];
	{a*theT^NN, (b + n a Last[ld]/theT)theT^NN, theT^(NN - n)g, theT^(-n)}
]

ParamRdeSpecialDenominator[a_, b_, g_List, lv_List, ld_List]/;HyperTangentMonomialQ[lv ,ld]:=
Module[{nb, nc, p, n, alpha, beta, eta, NN, theT, toCheck, s, m, nn, v, theta},
	theT = Last[lv];
	p = theT^2 + 1;
	nb = OrderNu[p, b, theT];
	nc = OrderNu[p, g, theT]; 
	n = Min[ 0, nc - Min[0, nb] ];
	If[ nb == 0,
		{alpha, beta} = { myIm[#], myRe[#] }& @ Remainder[-b/a, p, theT];
		eta = PolynomialQuotient[Last[ld], p, theT]; (* exact division *)
		toCheck = LogarithmicDerivativeQ[ 2*beta, Most[lv], Most[ld] ];
		If[ First[toCheck] === True,
			toCheck = ParametricLogarithmicDerivative[ alpha I + beta, theta, 2 eta I theta, Most[lv], Most[ld] ];
			If[ First[toCheck] =!= NoSolution,
				{nn, s, v} = toCheck;
				If[nn === 1 && FreeQ[v, theT],
					n = Min[n, s]
				]
			]
		]
	];
	NN = Max[0, -nb];
	{a p^NN, b*p^NN + n*a*Derivative[lv, ld][p]p^(NN-1), g*p^(NN-n), p^(-n)}
]

ParamRdeSpecialDenominator[___]:= NoSolution
		

LinearConstraints[a_,b_,g_List,lv_List,ld_List]:=
Module[{ d, qq, vv, rr,qiri, theT },
(* Given a derivation DD on k(t), a,b in k[t] and g1,..,gm in k(t), return 
   q1,..,qm in k[t] and a matrix MM with entries in k(t) such that for any
   solution c1,..,cm in Const(k) and p in k[t] of a*DD[p]+b*p = c1*g1+..+cm*gm,
   {c1,..,cm} is a solution of MM*x=0, and p and the ci's satisfy 
   a*DD[p]+b*p = c1*q1+..+cm*qm *)
	theT = Last[lv];
	d = PolynomialLCM @@ Denominator[ Together[g] ];
	qiri = PolyDivide[ #, d, theT ]& /@ Together[d*g];
	qq = First /@ qiri;
	rr = Last /@ qiri;
	{qq, Transpose[ PadRight[ CoefficientList[ rr, theT ] ] ]} (* <-- MM *)
]
Clear[ConstantSystem];

ConstantSystem[{},{},lv_List,ld_List]:={ {}, {} };

ConstantSystem[A_?MatrixQ,u_?VectorQ,lv_List,ld_List] /; (Length[A] == Length[u]) :=
Module[{ AA, um1, uu, s, j, i, Rm1, m, a, DD, theT, k, pos, dA },
(* Given a differential field (K, D) with constant field C, a matrix A and a vector u with coeffiecients in K,
   returns a matrix B with coefficients in C and a vector v such that either v has coefficients in C, in wich
   case the solutions in C of A*x = u are exactly the solutions of B*x = v, or v has a nonconstant coefficient,
   in which case A*x = u has no constant soltuion *)
	theT = Last[lv];
	AA = SparseArray[RowReduce[ PadLeft[ Join[A, Thread[{u}], 2] ] ]];
	uu = AA[[All,-1]];
	AA = AA[[All,1;;-2]];
    DD = Derivation[lv, ld];
    While[True,
    	dA = Together[DD[AA]];
    	m = Most[ArrayRules[dA]];
    	(* ordering arrayrules so that it is ordered 
    	   by column then row indexes *)
    	m = m[[ Ordering[ m[[All,1,{2,1}]] ] ]];
    	pos = Position[ 
    		     m[[All,2]], 
    		     y_ /; NonZeroPolynomialQ[Numerator[y], theT], 
    		     {1}, 1, Heads -> False];
    	If[pos==={}, Break[] ];
    	{i,j} = First[m[[First[Flatten@pos]]]];
 		Rm1 = dA[[i]]/dA[[i,j]] ;
 		um1 = DD[ uu[[i]] ]/dA[[i,j]];
		uu = SparseArray@Join[ uu - AA[[All,j]] um1, {um1} ];
		AA = SparseArray@Join[ AA - Outer[ Times, AA[[All, j]], Rm1 ], {Rm1} ];
    ];
    (* remove zero rows of AA which have corresponding zero entries in uu *)
   (*Transpose[DeleteCases[Thread[{AA // Together, uu}],{{0..},0},{1}]]*)
   {AA //Normal, uu}
]


(* Parametric Bound for the degree of q in the case where D = d/dt *)
ParamRdeBoundDegree[a_,b_,q_List,lv_List,ld_List]/;
With[{t = Last[lv] }, 
  	{lv, ld} === {{t},{1}} && PolynomialQ[a, t] && PolynomialQ[b, t] && 
  	NonZeroPolynomialQ[a, t] &&  ArrayQ[q, _, PolynomialQ[#, t]& ] ]:=
Module[{theT, da, db, dc, s, n},
	DRPrint["Visit ParamRdeBoundDegree case D = d/d",Last[lv],"."];
	DRPrint["	Entries: a = ", a ,", b = ", b , ", q = ", q, ", {lv, ld} = ", {lv, ld}, "."];
	theT = Last[lv];
	{da, db} = Exponent[{a, b}, theT];
	dc = Max[ Exponent[q, theT] ];
	n = Max[0, dc - Max[db, da - 1]];
	If[db == da - 1,
		s = lc[b, theT]/lc[a, theT]//Together;
		If[IntegerQ[s], n = Max[0, s, dc - db] ]
	];
	DRPrint["Exit ParamRdeBoundDegree case D = d/d",Last[lv],"."];
	DRPrint["	Output: n = ", n, "."];
	n
]

(* Parametric Bound for the degree of q in the primitive case*)
ParamRdeBoundDegree[a_,b_,q_List,lv_List,ld_List]/;PrimitiveMonomialQ[lv, ld]&& {ld} =!= {1} &&
With[{t=Last[lv]}, PolynomialQ[a, t] && PolynomialQ[b, t] && 
	  NonZeroPolynomialQ[a, t] && Fold[Function[{pr, el}, pr && PolynomialQ[el, t]], True, q] ]:=
Module[{ da, db, dc, alpha, beta, z, n, DD, theT, toCheck, s, conditional, w},
(* Given a derivation DD on k[t] and a,b,q1,..,qm in k[t] with DD[t] in k and
   a !=0, return n in Z such that deg(q) <=n for any c1,..,cm in Const[k] and 
   q in k[t] of a DD[q]+b*q = Sum[ci*qi] 
*)    
	DRPrint["Visit ParamRdeBoundDegree primitive case."];
	DRPrint["	Entries: a = ", a ,", b = ", b , ", q = ", q, ", {lv, ld} = ", {lv, ld}, "."];
    theT = Last[lv];
    DD = Derivation[lv, ld];
    {da, db} = Exponent[ {a, b}, theT ];
    dc = Max[Exponent[q, theT]];
    If[db > da,
    	n = Max[0, dc - db],
    (*Else*)
    	n = Max[0, dc - da + 1]
    ];
    If[db == da -1,
    	alpha = -lc[b, theT]/lc[a, theT];
		toCheck = LimitedIntegrate[ alpha, {Last[ld]}, Most[lv], Most[ld] ]; 
		(* returns {z,{s}} s.t. alpha = s DD[theT]+DD[z] *)
		If[toCheck =!= NoSolution, 
			{z,{s}} = toCheck;
			If[IntegerQ[s], n = Max[n, s]];
		];
    ];
    If[db == da,
    	alpha = -lc[b, theT]/lc[a, theT];
    	{conditional, z} = LogarithmicDerivativeQ[ alpha, Most[lv], Most[ld] ];
    	(* returns {True, z} or {False,$Failed}, s.t. alpha = Dz/z *)
    	If[conditional,
    		beta = -lc[a DD[z] + b*z, theT]/(z lc[a, theT]);
    		toCheck = LimitedIntegrate[ beta, {Last[ld]}, Most[lv], Most[ld] ];
    		(* returns {w,{s}} s.t. beta = s DD[theT] + DD[w] *)
    		If[toCheck =!= NoSolution, 
			{z, {s} } = toCheck;
			If[IntegerQ[s], n = Max[n, s] ];
			];
    	];
    ];
    DRPrint["Exit ParamRdeBoundDegree primitive case."];
    DRPrint["	Output: n = ", n ,"."];
    n
]

(* Parametric Bound for the degree of q in the non-linear case, for now it is restricted to HyperTangent. *)
ParamRdeBoundDegree[a_,b_,q_List,lv_List,ld_List]/;HyperTangentMonomialQ[lv,ld]&&
With[{t = Last[lv]}, PolynomialQ[a, t] && PolynomialQ[b, t] && 
  	NonZeroPolynomialQ[a, t] &&  ArrayQ[q, _, PolynomialQ[#,t]& ]]:=	
Module[{theT, da, db, dc, delta, lambda, Dt, n, s},
	DRPrint["Visit ParamRdeBoundDegree hypertangent case."];
	DRPrint["	Entries: a = ", a ,", b = ", b , ", q = ", q, ", {lv, ld} = ", {lv, ld}, "."];
	theT = Last[lv];
	Dt = Last[ld];
	delta = Exponent[Dt, theT];
	lambda = lc[Dt,theT];
	{da, db} = Exponent[{a, b}, theT];
	dc = Max[ Exponent[q, theT] ];
	n = Max[0, dc - Max[da + delta -1, db] ];
	If[db == da + delta -1,
		s = -lc[b, theT]/(lambda lc[a, theT]);
		If[IntegerQ[s], n = Max[0, s, dc - db] ]
	];
	DRPrint["Exit ParamRdeBoundDegree hypertangent case."];
    DRPint["	Output: n = ", n ,"."];
	n	
]

(* Parametric Bound for the degree of q in the HyperExponential case. *)
ParamRdeBoundDegree[a_,b_,q_List,lv_List,ld_List]/;HyperExponentialMonomialQ[lv,ld]&&
With[{t = Last[lv]}, PolynomialQ[a, t] && PolynomialQ[b, t] && 
  	NonZeroPolynomialQ[a, t] &&  ArrayQ[q, _, PolynomialQ[#,t]& ]]:=	
Module[{theT, da, db, dc, Dt, n, s, alpha, toCheck, z, m},
	theT = Last[lv];
	Dt = Last[ld];
	{da, db} = Exponent[{a, b}, theT];
	dc = Max[ Exponent[q, theT] ];
	n = Max[0, dc - Max[da , db] ];
	If[db == da,
		alpha = -lc[b, theT]/lc[a, theT];
		toCheck = ParametricLogarithmicDerivative[ alpha, theT, Dt, Most[lv], Most[ld] ]; (* Heuristic *)
		If[First[toCheck] =!= $Failed,
			{m, s, z} = toCheck; (* m and s are integers *)
			If[m === 1,
				n = Max[n, s]
			];
		(* Else *)
			If[Last[toCheck] === 0, (* <- This means that the 'heuristic' method failed. So, I'll put my own bound *)
				n = Max[n, 5]
			]
		]
	];
	DRPrint["Exit ParamRdeBoundDegree hyperexponential case."];
    DRPint["	Output: n = ", n ,"."];
	n	
]

(* Parametric Special Polynomial Differential Equation *)	  	  
ParamSPDE[a_,b_,q_List,lv_List,ld_List,n_]:=
Module[{theT, m, riANDzi, ri, zi, secondEntry, DD},
	DD = Derivation[lv, ld];
	theT = Last[lv];
	riANDzi = fastExtendedEuclidean[b, a, #, theT]& /@ q;
	ri = First /@ riANDzi;
	zi = Last /@ riANDzi;
    { a, b + DD[a], zi - DD[ri],  ri,  n - Exponent[a, theT] }
]

ReduceToParamPolyRischDE[a_,b_,q_List,lv_List,ld_List,n_Integer,forqMatrix_:{},forqA_:{}, ConstraintsMatrix_:{}]/;
With[{t = Last[lv]}, PolynomialQ[a, t] && PolynomialQ[b, t] && 
Fold[Function[{pr, el}, pr && PolynomialQ[el, t]], True, q]]:=
(* Transform an equation of the form a*q+b*D[q]=Sum[ci*qi] with a,b in k[t] to
   one of the form p+b*D[p] = Sum[ci*qi] with b,qi in k[t]
   
   Output: Either $Failed or {1,b, {q1,..,qm},n,A,Mq,Mc} such that p+b*D[p] = Sum[ci*qi]
           Mq: the matrix to be used to construct q once we know p. 
           A: vector used to construct q once we know p.
           Mc: the matrix to be used to construct the ci's.  
   
   Note: We don't need the first entry in the ouput at all, but I'll leave it in there.  If it happends that
   		 the first entry is not 1, then there is a problem with this algorithm. *)
Module[{aa, bb, qq, nn, g, theT, r, RR, CC, ConstraintsM = {}, AA },
	If[n < 0, 
		DRPrint["Failure comming from ReduceToParamPolyRischDE. It fails to transform an equation of the form a Dp + b p = Sum[ci qi]" ];
		DRPrint["to one of the form Dp + b p = Sum[ci qi]."];
		DRPrint["	Entries: a = ", a, ", b = ", b, ", and q's = ", q ,"."]; 
		Return[NoSolution]
	];
	theT = Last[lv];
	{aa, bb, qq, nn} = {a, b, q, n};
	g = PolynomialGCD[aa, bb];
    If[!FreeQ[g, theT] (* GCD not trivial *),
		{aa, bb, qq} = {aa, bb, qq}/g //Together;
		{qq, ConstraintsM} = LinearConstraints[aa, bb, qq, lv, ld]
    ];
	{aa, bb, qq, r, nn} = ParamSPDE[aa, bb, qq, lv, ld, nn];
	RR = Join[ forqMatrix, {r} ];   	            		  (* <- this matrix is needed to reconstruct the q *)
	CC = PadRight[ Join[ ConstraintsMatrix, ConstraintsM ] ]; (* <- this matrix is needed for the constraints *)
	AA = Join[ forqA, {aa} ];                       		  (* <- this is needed to reconstruct the q *)
	If[Exponent[aa, theT] > 0,
		ReduceToParamPolyRischDE[ aa, bb, qq, lv, ld, nn, RR, AA, CC ],
		{Together[aa/aa], Together[bb/aa], Together[qq/aa], nn, RR , AA, CC}
	]	
]

(* Polynomial Parametric Risch DE Non-Cancellation case 1. *)
ParamPolyRischDE[b_,qq_List,lv_List,ld_List,nn_]/;
With[{t = Last[lv], ht = Last[ld]}, 
  	PolynomialQ[b, t]&& NonZeroPolynomialQ[b, t]
  	 && ( {lv, ld} === { {t}, {1} } || Exponent[b, t] > Max[ 0, Exponent[ht, t] - 1 ] ) && 
  	 Fold[ Function[ {pr, el}, pr && PolynomialQ[el, t] ], True, qq ]
  	  ]:=
Module[{db, bd, q, s, h, m, n, A, u, theT, DD, i, j, MM, indx},
(* Given a derivation DD on k[t], n in Z and b,q1,..,qm in k[t] with b!=0
   and either DD = d/dt or deg[b]>Max[0,delta-1], returns h1,..,hr in k[t]
   and a matrix A with coefficients in Const(k) such that if c1,..,cm in Const(k)
   and q in k[t] satisfy deg(q)<=n and DD[q]+b*q=Sum[ci] then q = Sum[dj*hj,{j,r}]
   where d1,..,dr in Const(k) and A.{c1,..,cm,d1,..,dr}=0 *)
    DRPrint["Visit ParamPolyRischDE non-cancellation case 1."];
    DRPrint[ "	Entries: b = ", b, ", g = ", qq, ", {lv, ld} = ", {lv, ld}, ", n = ", nn , "."];
    theT = Last[lv];
    DD = Derivation[lv, ld];
    {db, bd, n, q} = {Exponent[b, theT], lc[b, theT], nn, qq};
    m = Length[q];
    h = ConstantArray[0, m];
    While[n >= 0,
    	s = Coefficient[#, theT, n + db]/bd & /@ q;
    	h = MapThread[(#1 + #2*theT^n)&, {h, s}];
    	q = MapThread[(#1 - DD[#2*theT^n] - b*#2*theT^n)&, {q, s}];
    	n = n - 1
    ];
    MM = Transpose[ PadRight[ CoefficientList[q, theT] ] ];
	{A, u} = ConstantSystem[ MM, ConstantArray[ 0, Length[MM] ], lv, ld ];
    A = PadRight[Join[A, Join[IdentityMatrix[m], -IdentityMatrix[m], 2] ]];
	DRPrint["Exit ParamPolyRischDE non-cancellation case 1."];
   	{h, DeleteCases[A, {0..}]}
]

(* Polynomial Parametric Risch DE Non-Cancellation case 2. *)
ParamPolyRischDE[b_,g_List,lv_List,ld_List,nn_]/;
With[{t = Last[lv]},
	PolynomialQ[b , t] && Exponent[b, t] < Exponent[ Last[ld], t ] - 1 &&
	( {lv, ld} === { {t}, {1} } || Exponent[ Last[ld], t ] >= 2)
]:=
Module[{delta, lambda, h, s, A, MM, u, f, B, dc, DD, theT, m, i, j, toCheck, r, q, n, f1, f2, indx},
(* Given a derivation DD on k[t], n in Z and b,q1,..,qm in k[t] with
   deg[b,t]<delta(t)-1 and either DD = d/dt or delta(t)>=2, returns
   h1,..,hr in k[t] and a matrix A with coefficients in Const(k) such that 
   if c1,..,cm in Const(k) and q in k[t] satisfy deg(q)<=n and DD[q]+b*q
   = Sum[ci] then q = Sum[dj*hj] in Const(k) and A(c1,..,cm,d1,..,dr) = 0 *)
    DRPrint["Visit ParamPolyRischDE non-cancellation case 2."];
    DRPrint[ "	Entries: b = ", b, ", g = ", g, ", {lv, ld} = ", {lv, ld}, ", n = ", nn , "."];
    theT = Last[lv];
    DD = Derivation[lv, ld];
    {delta, lambda, q, n} = { Exponent[ Last[ld], theT ], lc[ Last[ld], theT ], g, nn };
    m = Length[q];
    h = ConstantArray[0, m];
    While[n > 0,
    	s = Coefficient[q, theT, n + delta - 1]/(n*lambda);
    	h = MapThread[(#1 + #2*theT^n)&, {h, s}];
    	q = MapThread[(#1 - DD[#2*theT^n] - b*#2*theT^n)&, {q, s}];
    	n = n - 1
    ];
    q = Together[q];
    If[Exponent[b,theT] > 0,
    	s = Coefficient[q, theT, Exponent[b, theT]]/(lc[b, theT]);
    	h = MapThread[(#1 + #2)&, {h, s}];
    	q = MapThread[(#1 - DD[#2] - b*#2)&, {q, s}];
    	MM = Transpose[ PadRight[ CoefficientList[q, theT] ] ];
    	{A, u} = ConstantSystem[ MM, ConstantArray[ 0, Length[MM] ], lv, ld ];
    	A = PadRight[ Join[ A, Join[IdentityMatrix[m], -IdentityMatrix[m], 2] ] ];
    	DRPrint["Exit ParamPolyRischDE non-cancellation case 2."];
	    {h, DeleteCases[A, {0..}]}, 
    (*Else*)
        toCheck = ParamRischDE[ b, q/.theT->0, Most[lv], Most[ld] ];
        If[toCheck === NoSolution,
        	DRPrint["Failure comming from ParamPolyRischDE non-cancellation case 2."];
        	Return[NoSolution]
        ];
        {f, B} = toCheck;
        r = Length[f];
        MM = Transpose[ PadRight[ CoefficientList[q, theT] ] ];
        If[MM =!= {}, 
        	MM = PadRight[ Join[MM, {-DD[#] - b*#& /@ f}, 2]],
        (*Else*)
        	MM = {-DD[#] - b*#& /@ f} 
        ];
       	{A, u} = ConstantSystem[ MM, ConstantArray[ 0, Length[MM] ], lv, ld ];
        A = PadRight[ Join[A, B] ];
		A = PadRight[ Join[ A, 
			  Join[ IdentityMatrix[m], 
			  		ConstantArray[0, {m, r}], 
			  	   -IdentityMatrix[m], 2 ] ] ];
		h = Join[f, h];
		DRPrint["Exit ParamPolyRischDE non-cancellation case 2."];
		{h, DeleteCases[A, {0..}]}
    ]
]

(* ============== Auxiliary functions for the Cancellation case 1 ========================= *)
SpecialParamRischDE[b_,g_List, lv_List, ld_List, n_]/;PrimitiveMonomialQ[lv, ld]:= 
With[{bb = b, gg = g},
(* Not intended to be visible by the user *)
	ParamRischDE[ b, Coefficient[ g, Last[lv], n ], Most[lv], Most[ld] ]
]
SpecialParamRischDE[b_,g_List, lv_List, ld_List, n_]/;HyperExponentialMonomialQ[lv, ld]:= 
(* Not intended to be visible by the user *)
With[{t = Last[lv], Dt = Last[ld]},
	ParamRischDE[ b + n*Dt/t, Coefficient[ g, t, n ], Most[lv], Most[ld] ]
];
(* ========================= End of Auxiliary functions ==================================== *)

(* Polynomial Parametric Risch DE Cancellation case 1 *)
ParamPolyRischDE[b_,g_List,lv_List,ld_List,nn_]/; (PrimitiveMonomialQ[lv, ld] || HyperExponentialMonomialQ[lv, ld]) &&
Exponent[ Last[ld], Last[lv] ] <=1 && FreeQ[b, Last[lv]] && ld=!={1} :=
Module[{theT, f, A1, AA, F, DD, gg, m, n, r, zero, H, MM, toCheck, m1, indx, g1, g2},
    DRPrint["Visit ParamPolyRischDE cancellation case 1."];
    DRPrint[ "	Entries: b = ", b, ", g = ", g, ", {lv, ld} = ", {lv, ld}, ", n = ", nn , "."];
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{m1, n} = {Length[g], nn};
	toCheck = SpecialParamRischDE[ b, g, lv, ld, n ];
	If[toCheck === NoSolution,
		DRPrint["Failure comming from ParamPolyRischDE cancellation case 1."];
		Return[NoSolution]
	];
	{f, AA} = toCheck;
	gg = Join[ g, -b*f*theT^n - DD[f theT^n] ];
	F = {f};
	n = n - 1;
	While[n >= 0,
		toCheck = SpecialParamRischDE[ b, gg, lv, ld, n ];
		If[toCheck === NoSolution,
			DRPrint["Failure comming from ParamPolyRischDE cancellation case 1."];
			Return[NoSolution]
		];
		{f, A1} = toCheck;
		gg = Join[ gg, - b*f*theT^n - DD[f*theT^n] ];
		AA = PadRight[ Join[AA, A1] ];
		F = Join[F, {f}];
		n = n - 1
	];
	H = Flatten [MapThread[ Times, {F, Table[ theT^(nn - i), {i, 0, nn} ] } ] ];
	If[gg === ConstantArray[0, Length[gg] ],
		MM = {gg},
		MM = Transpose[ PadRight[ CoefficientList[gg, theT] ] ]
	];
	AA = PadRight[ Join[MM, AA] ];
	{AA, zero} = ConstantSystem[AA, ConstantArray[0, Length[AA] ], lv, ld];
	DRPrint["Exit ParamPolyRischDE cancellation case 1."];
    {H, DeleteCases[AA, {0..}]}
]

ParamRischDE[0,g_List,{},{}]/;g === ConstantArray[0, Length[g] ] :=
With[{m = Length[g]},
	DRPrint["Visit ParamRischDE first boundary."];
	DRPrint[ "	Entries: f = ", 0, ", g = ", g, ", {lv, ld} = ", { {}, {} }, "."];
	DRPrint["Exit ParamRischDE first boundary."];
	{ConstantArray[ 1, 2m ], Join[IdentityMatrix[m], -IdentityMatrix[m], 2]}
	(*{ConstantArray[1,m], {g}}*)
]

ParamRischDE[0,g_List,lv_List,ld_List]/;{lv, ld} =!= {{},{}} && With[{t = Last[lv]}, ZeroPolynomialQ[g, t] ] := 
With[{m = Length[g]},
	DRPrint["Visit ParamRischDE second boundary."];
	DRPrint[ "	Entries: f = ", 0, ", g = ", g, ", {lv, ld} = ", {lv, ld}, "."];
	DRPrint["Exit ParamRischDE second boundary."];
	{ConstantArray[1, 2m], Join[IdentityMatrix[m], -IdentityMatrix[m], 2]}
]

ParamRischDE[b_,g_List,lv_List,ld_List]/;( {lv, ld} =!= { {}, {} } )&& With[{t = Last[lv]},
	NonZeroPolynomialQ[b, t] && ZeroPolynomialQ[g, t] ]:= 
With[{m = Length[g]},
	DRPrint["Visit ParamRischDE third boundary."];
	DRPrint["	Entries: f = ", b , ", g = ", g, ", {lv, ld} = ", {lv, ld}, "."];
	{ConstantArray[0, m], {} }
]

(* Since we are solving the parametric Risch Differential Equation within the field, then entries = { f, g, {}, {} }
   means that we are solving the ParamRischDE over the constant field (e.g. over Q, R, C, etc) and so D(y)=0.  Then 
   if f !=0 then then y = (c1g1 + .. cmgm)/f is the general solution.*)
ParamRischDE[f_?NumericQ, g_List, {}, {}]/;(f != 0):=With[{ff = f},
	DRPrint["Visit ParamRischDE forth boundary."];
	DRPrint["	Entries: f = ", f , ", g = ", g, ", {lv, ld} = ", { {}, {} }, "."];
	{ g/ff, {} };
];
(* Since we are solving the parametric Risch Differential Equation within the field, then entries = { 0, g, {}, {} }
   means that we are solving the ParamRischDE over the constant field (e.g. over Q, R, C, etc) and so D(y)=0. But 
   since f = 0 we have 0 = c1g1 + .. cmgm and h = {1,...,1} *)
ParamRischDE[0, g_List, {}, {}]/;Fold[ Function[{pr, el}, pr && NumericQ[el] ], True, g]:= With[{gg = g},
	DRPrint["Visit ParamRischDE fifth boundary."];
	DRPrint["	Entries: f = ", 0 , ", g = ", g, ", {lv, ld} = ", { {}, {} }, "."];
	{ConstantArray[ 1, Length[gg] ], {gg}}
]
	
ParamRischDE[f_,g_List,lv_List,ld_List]:=
Module[{q1, G, F, AA, A1, n, h1, h2, h, A, Q, DD, theT, a, b, v, RR, zero, toCheck, aVec, m, block, f1, f2, indx, indx1},
	DRPrint["Visit ParamRischDE."];
	DRPrint["	Entries: f = ", f , ", g = ", g, ", {lv, ld} = ", { lv, ld }, "."];
		
	theT = Last[lv];
	DD = Derivation[lv,ld];
	m = Length[g];
	q1 = WeakNormalizer[f,lv,ld];
	F = f - DD[q1]/q1 //Together;
	G = q1*g;
	{a, b, G, h1} = ParamRdeNormalDenominator[F, G, lv, ld];
	toCheck = ParamRdeSpecialDenominator[a, b, G, lv, ld];
	If[toCheck === $Failed,
	(* This can only happend in the hyperexponential case because ParametricLogarithmicDerivative is heuristic *)
		DRPrint["Failure comming from ParamRischDE.  Reason: heuristic method."];
		Return[$Failed]
	];
	{a, b, G, h2} = toCheck;
	{G, AA} = LinearConstraints[a, b, G, lv, ld];
	{AA, zero} = ConstantSystem[ AA, ConstantArray[ 0, Length[ AA ] ], lv, ld ];
	n = ParamRdeBoundDegree[a, b, G, lv, ld];
	toCheck = ReduceToParamPolyRischDE[a, b, G, lv, ld, n];
	If[toCheck === $Failed,
		DRPrint["Failure comming from ParamRischDE.  Reason: a failure comming from ReduceToParamPolyRischDE."];
		Return[$Failed]
	];
	{a, b, G, n, RR, aVec, A1} = toCheck//Together;
	AA = PadRight[ Join[AA, A1] ];
	toCheck = ParamPolyRischDE[b, G, lv, ld, n];
	If[toCheck === NoSolution,
		DRPrint["Failure comming from ParamRischDE. Reason: a failure comming from ParamRischDE."];
		Return[NoSolution]
	];
	{h, A1} = toCheck;
	AA = PadRight[ Join[AA, A1] ];
	RR = Transpose[RR];
	aVec = Table[ Times @@ Drop[aVec, i], {i, 0, Length[aVec]} ];
	(* if a = (a1, a2, a3) then I'm creating (a1a2a3, a1a2, a1, 1) *)
	RR = Drop[ aVec, 1 ].Reverse[ # ] & /@ RR;
	h = Join[RR, First[aVec]h]/(q1 h1 h2);

	indx = Intersection[Position[h, 0, {1}], Position[Transpose[AA], {0..}, {1}] ];
	indx = DeleteCases[indx, {x_} /; x <= m ];
	indx = Complement[ Range[Length[h]], Flatten[indx] ];
	h = Part[h, indx];
	AA = AA[[ All, indx ]];
	DRPrint["Exit ParamRischDE."];
	{h, AA//Together}
]	

ParamRischDE[___]:=NoSolution;

LimitedIntegrateReduce[f_,w_List,lv_List,ld_List]/;
(PrimitiveMonomialQ[lv, ld] || HyperExponentialMonomialQ[lv, ld] || HyperTangentMonomialQ[lv, ld])&& IrrSpecialsAreOfFirstKindQ[lv, ld]:=
Module[{dn, ds, en, es, c, hn, hs, a, b, NN, mu, delta, num, den, m,list, theT, DD},
	theT = Last[lv];
	delta = Exponent[ Last[ld], theT ];
	DD = Derivation[lv, ld];
	{num, den} = NumeratorDenominator[f];
	{dn, ds} = SplitFactor[den, lv, ld];
	list = SplitFactor[#, lv, ld]& /@ Denominator[ Together[w] ];
	en = First /@ list;
	es = Last /@ list;
	c = PolynomialLCM @@ Join[{dn}, en];
	hn = PolynomialGCD[c, D[c, theT] ];
	a = hn;
	b = - DD[a];
	NN = 0;
	hs = PolynomialLCM @@ Join[{ds},es];
	a = hn*hs;
	b = - DD[hn]-hn*DD[hs]/hs //Together;
	mu = Min[ Join[{ OrderNu[Infinity, f, theT]}, OrderNu[Infinity, w, theT] ] ];
	NN = Exponent[hn,theT] + Exponent[hs, theT] + Max[0, 1 - delta - mu];
	Collect[{a, b, a, NN, a*hn*f,-a*hn*w},theT,Together]
]

LimitedIntegrateReduce[___]:= NoSolution

Clear[LimitedIntegrate];

LimitedIntegrate[f_?NumericQ,w_List,{},{}]/;(Fold[Function[{pr, el}, pr && NumericQ[el]], True, w] &&
w =!= ConstantArray[0, Length[w] ] && Total[w] =!= 0):=
	With[{m = Total[w]},
		{0, ConstantArray[f/m, Length[w]] }
]

LimitedIntegrate[f_?NumericQ,w_List,{},{}]/;(f !=0 && Fold[Function[{pr, el}, pr && NumericQ[el]], True, w] &&
w === ConstantArray[0, Length[w] ]):= NoSolution;

LimitedIntegrate[0,w_List,{},{}]/;(Fold[Function[{pr, el}, pr && NumericQ[el]], True, w] &&
w === ConstantArray[0, Length[w]]):={0, ConstantArray[0, Length[w]]};
	
LimitedIntegrate[f_,w_List,lv_List,ld_List]/;
(PrimitiveMonomialQ[lv,ld] || HyperExponentialMonomialQ[lv, ld] || HyperTangentMonomialQ[lv,ld]):=
Module[{a,b,h,h1,n,g,v,GG,M,zeroVec,nullA,constants, theT, firstEntry, m, toCheck, q, A, ci, RR, CC,aVec,vec},
	DRPrint["Visit LimitedIntegrate."];
	DRPrint["	Entries: f = ", f , ", w = ", w, ", {lv, ld} = ", {lv, ld}, "."];
	theT = Last[lv];
	(* Next step reduces the problem to a*Dp + b*p = g + c1*v1 + .. + cm*vm *)
	toCheck = LimitedIntegrateReduce[f, w, lv, ld];
	If[toCheck === NoSolution,
		Return[NoSolution]
	];
	{a, b, h1, n, g, v} = toCheck;
	GG = Join[{g},v]; 
	m = Length[GG];
	{GG, M} = LinearConstraints[a, b, GG, lv, ld];
	{M, zeroVec} = ConstantSystem[M, ConstantArray[0, Length[M] ], lv, ld];	
	toCheck = ReduceToParamPolyRischDE[a, b, GG, lv, ld, n];
	If[ toCheck === NoSolution,
		DRPrint["Failure comming from LimitedIntegrate.  Reason: Failure came from ReduceToParamPolyRischDE."];
		Return[NoSolution]
	];
	{a, b, GG, n, RR, aVec, CC} = toCheck;
	M = PadRight[ Join[ M, CC ] ];
	toCheck = ParamPolyRischDE[b, GG, lv, ld, n];
	If[toCheck === NoSolution,
		DRPrint["Failure comming from LimitedIntegrate.  Reason: Failure came from ParamPolyRischDE."];
		Return[NoSolution]
	];
	{h, A} = toCheck;
	A = PadRight[ Join[M, A] ];
	If[A === {},
		DRPrint["Failure comming from LimitedIntegrate. (1)"];
		Return[NoSolution];
	];
	
	RR = Transpose[RR];
	aVec = Table[ Times @@ Drop[aVec, i], {i, 0, Length[aVec]} ];
	RR = Drop[ aVec, 1 ].Reverse[ # ] & /@ RR;
	h = Join[ RR, First[aVec]*h ]/h1;
	
	{A, zeroVec} = ConstantSystem[A, ConstantArray[ 0, Length[A] ], lv ,ld];
	nullA = NullSpace[A];
	If[nullA === {} ,
		DRPrint["Failure comming from LimitedIntegrate. (2)"];
		Return[NoSolution]
	];
	
	constants = FirstWithNonZeroFirstEntry[nullA, theT];
	If[constants === {},
		DRPrint["Failure comming from LimitedIntegrate. (3)"];
		Return[NoSolution]
	];
	If[constants[[2]] === 0,
		vec = FirstWithZeroFirstEntryAndNonZeroSecond[nullA, theT];
		If[ vec =!= {},
			constants = Total[{constants,vec}]
		];
	];
	constants = constants/First[constants];
	ci = Take[constants, m];
	{h.constants, Rest[ci]} 
]

LimitedIntegrate[___] := NoSolution

(* Parametric Logarithmic Derivative Heuristic, First boundary case. *)
ParametricLogarithmicDerivative[f_, theta_, dtheta_, {}, {} ]/;
(HyperExponentialMonomialQ[{theta}, {dtheta}] && RationalNumberQ[f] && RationalNumberQ[Together[dtheta/theta]]):=
Module[{a, b, m ,n},
	{a, b} = NumeratorDenominator[f];
	{m, n} = NumeratorDenominator[ Together[dtheta/theta] ];
	Return[{b m, a n, 1}]
]

(* Parametric Logarithmic Derivative Heuristic, First improvement. *)
ParametricLogarithmicDerivative[f_,theta_,dtheta_,lv_List,ld_List]/;
(HyperExponentialMonomialQ[Join[lv,{theta}], Join[ld, {dtheta}]] && NonZeroPolynomialQ[f, Last[lv]] &&
RationalNumberQ[(dtheta/theta)/f//Together]):=
With[{z = (dtheta/theta)/f // Together},
	{ Numerator[z], Denominator[z], 1}
];

(* Parametric Logarithmic Derivative Heuristic, Second improvement. *)
ParametricLogarithmicDerivative[f_,theta_,dtheta_,lv_List,ld_List]/;
(HyperExponentialMonomialQ[Join[lv,{theta}], Join[ld, {dtheta}]] && ZeroPolynomialQ[f, Last[lv]]):= {1, 0, 1};

(* Parametric Logarithmic Derivative Heuristic *)
ParametricLogarithmicDerivative[f_,theta_,dtheta_,lv_List,ld_List]/;
(HyperExponentialMonomialQ[Join[lv,{theta}], Join[ld, {dtheta}]]):=
Module[{w,denf,denw,p,a,q,b,BB,CC,s,NN,MM,LV,LD,DD,numf,numw,theT,conditional,theV,IntQ, lcm,lcmn,lcms,z},
(* This algorithm is heuristic i.e. it can fail to find a solution even if there is one.  For this reason an output
   of this algorithm is of the form {integer1, integer2, v} which says it found a solution or an output of the form
   {$Failed, b} where b = 0 or 1.  The output {$Failed, 0} means that the algorithm failed and it is possible that 
   there is a solution.  The output {$Failed, 1} means that the algorithm didn't fail and there is no solution. *)
	DRPrint["Visit ParametricLogarithmicDerivative."];
	DRPrint["	Entries: f = ", f, " ,theta = ", theta, ", dtheta = ", dtheta, ", {lv, ld} = ", {lv, ld},"."];
	theT = Last[lv];
	(*{LV, LD} = {Join[lv,{theta}], Join[ld, {dtheta}]};*)
	DD = Derivative[lv, ld];
	w = dtheta/theta // Together;
	{ {numf, denf}, {numw, denw} } = NumeratorDenominator /@ {f, w}; 
	{p, a} = PolyDivide[numf, denf, theT];
	{q, b} = PolyDivide[numw, denw, theT];
	BB = Max[ 0, Exponent[ Last[ld], theT ] - 1 ];
	CC = Max[ Exponent[p, theT], Exponent[q, theT] ];
	If[Exponent[q, theT] > BB,
		s = RationalMultipleCoefficients[p, q, theT, BB + 1, CC];
		If[s === NoSolution,
			Return[{NoSolution, 1}]
		];
		{MM, NN} = NumeratorDenominator[s]; (* <- There is a typo in the book.  This is the correct order! *)
		{ conditional, IntQ, theV } = RadicalLogarithmicDerivativeQ[NN*f - MM*w, lv, ld];
		If[conditional,
			Return[{IntQ*NN, IntQ*MM, theV}],
		(*Else*)
			Return[{NoSolution, 1}]
		]
	];
	If[Exponent[p, theT] > BB,
		Return[{NoSolution, 1}]
	];
	lcm = PolynomialLCM[denf, denw];
	{lcmn, lcms} = SplitFactor[lcm, lv, ld]; 
	z = lcms * PolynomialGCD[ lcmn, D[lcmn, theT] ];
	If[ FreeQ[z, theT],
		{conditional, NN, theV} = RadicalLogarithmicDerivativeQ[f, lv, ld];
		If[conditional,
			Return[{NN, 0, theV}],
		(*Else*)
			DRPrint[" Failure comming from ParametricLogarithmicDerivative being heuristic."];
			Return[{$Failed, 0}]
		]
	];
	{p, a} = PolyDivide[lcm*f, z, theT];
	{q, b} = PolyDivide[lcm*w, z, theT];
	s = RationalMultipleCoefficients[ a, b, theT, 0, Exponent[z, theT] ];
	If[s === NoSolution,
		Return[{NoSolution, 1}]
	];
	{MM ,NN} = NumeratorDenominator[s];
	{ conditional, IntQ, theV } = RadicalLogarithmicDerivativeQ[NN*f - MM*w, lv, ld];
	If[conditional,
		Return[{IntQ*NN, IntQ*MM, theV}],
	(*Else*)
		Return[{NoSolution, 1}]
	]
]