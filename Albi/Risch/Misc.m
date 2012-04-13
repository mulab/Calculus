(* ::Package:: *)

(* Integration of Elementary Function, algorithms from book 
   Symbolic Integration, by M. Bronstein 
   
   Authors: Luis A. Medina and Sasha Pavlyk
   
   Mathematica Version: 6.1
   
   *)


SetAttributes[deg, Listable];
deg[poly_,var_]:= Max[0,Exponent[poly,var]];


NoSolution = $Failed;

Clear[DRPrint];
DRPrint[w___] /; ($DebugRisch === True) := Print[w];

RandomPoly[deg_, boundCoeff_, x_] := 
(* Input: degree (deg) and bound for the coefficients (boundCoeff)
   Output: a random polynomial in x of degree deg and coefficients in Z
           with the property that Abs (a[i])<= boundCoeff *)
  Total[Table[(-1)^RandomInteger[1]RandomInteger[boundCoeff] x^i, {i, 0, deg - 1}]] + 
    RandomInteger[{1, boundCoeff}] x^deg;

(* Returns a random Rational Function in x with deg (num) = deg1, deg (den) = deg2, and coefficient with 
   the property Abs (a[i])<= boundCoeff *)
RandomRF[deg1_, deg2_, boundCoeff_, x_] := RandomPoly[deg1, boundCoeff, x]/RandomPoly[deg2, boundCoeff, x]

(* Returns the integral of a polynomial *)
PolyInt[f_, x_] /; PolynomialQ[f, x] := 
 Collect[x f, x] /. (x^n_ :> x^n/n)


(* Returns the leading coefficient of poly as a polynomial in x *)
lc[poly_,var_]:= 
Coefficient[poly,var,deg[poly,var]]


content[A_,var_] :=GCD @@ (CoefficientList[A, var])
pp[A_,var_] := 
Collect[A/content[A,var],var]


PolyContentPP[A_,t_]:= 	With[{q = FactorTermsList[A,t]},
(* Returns the content and the primitive part of A as a poly in t *)
	   	{Times@@Most[q],Last[q]}
]
PolyContent[A_,t_]:= First[PolyContentPP[A,t]]
PolyPP[A_,t_]:= Last[PolyContentPP[A,t]]

NumeratorDenominator[f_]:=Through[ {Numerator, Denominator}[ Together[f] ] ]

NumeratorPrimitiveDenominator[f_,t_]:= Module[{num, den, cont},
	{num, den} = NumeratorDenominator[f];
	{cont, den} = PolyContentPP[den, t];
	{num/cont, den}
]

Derivation[lv_List, ld_List] :=
 Function[ u, ld.Table[ D[u, k], {k, lv}], Listable ]
 
mainVar[p_, lv_List]:= Catch[ Scan[If[ Exponent[p, #1] > 0, Throw[#1]]&, Reverse[lv]]; $Failed]

Clear[ZeroPolynomialQ];
ZeroPolynomialQ[poly_?NumberQ, var_] := (poly==0)
ZeroPolynomialQ[poly_, var_] := Module[{cl},
  PolynomialQ[poly, var] && (
	cl = Algebra`Polynomial`NestedTermsList[Expand[poly,var],var];
	Fold[Function[{pr, el}, pr && (el===0 || Together[el]===0)], True, cl[[All, -1]] ] )
]
ZeroPolynomialQ[polys_List, var_]:=Fold[Function[{pr,el}, pr && ZeroPolynomialQ[el, var] ], True, polys];

Clear[NonZeroPolynomialQ];
NonZeroPolynomialQ[poly_?NumberQ, var_] := (poly!=0);
NonZeroPolynomialQ[poly_, var_] := Module[{cl},
   PolynomialQ[poly, var] && (
	cl = Algebra`Polynomial`NestedTermsList[Expand[poly,var],var];
	cl =!= {} && 
	Fold[Function[{pr, el}, pr && Together[el]=!=0], True, cl[[All, -1]] ] )
];
NonZeroPolynomialQ[polys_List, var_]:=Fold[Function[{pr,el}, pr && NonZeroPolynomialQ[el, var] ], True, polys];

SubSet[A_, B_] := Length[Intersection[A,B]] == Length[Union[A]];
(* It turns out it needs Union for the case that the user or
   the machine returns a list with repetitions. *)
Clear[TrigToTan];
TrigToTan[ee_] := Module[{ToTan,e=ee/.Sec[x_]^2->1+Tan[x]^2},
  ToTan[Sin[x_]] = 
   With[{y = Together[x/2]}, 2 tan[y]/(1 + tan[y]^2)];
  (*ToTan[Tan[x_]] = 
   With[{y = Together[x/2]}, 2 tan[y]/(1 - tan[y]^2)];*)
  ToTan[Tan[x_]]:=tan[x]; 
  ToTan[Cos[x_]] = 
   With[{y = Together[x/2]}, (1 - tan[y]^2)/(1 + tan[y]^2)];
  ToTan[Sec[x_]^2]:=1+tan[x]^2;
  ToTan[Sec[x_]] = 
   With[{y = Together[x/2]}, (1 + tan[y]^2)/(1 - tan[y]^2)];
  ToTan[Csc[x_]] = 
   With[{y = Together[x/2]}, (1 + tan[y]^2)/(2 tan[y])];
  ToTan[Cot[x_]] = 
   With[{y = Together[x/2]}, (1 - tan[y]^2)/(2 tan[y])];
  e //. {x : (_Sin | _Cos | _Tan | _Cot | _Sec | _Csc) :> ToTan[x]}
  ]

Derivative[1][tan]=Function[1 + tan[#]^2]

(*TanToTrig[tan[y_]/(1 + tan[y_]^2)] := (1/2) Sin[2y];
TanToTrig[2 tan[y_]/(1 + tan[y_]^2)] := Sin[2y];
TanToTrig[(1 - tan[y_]^2)/(1 + tan[y_]^2)]:= Cos[2y];
TanToTrig[1+tan[x_]^2]:= Sec[x]^2;
TanToTrig[(1 + tan[y_]^2)/(1 - tan[y_]^2)]:=Sec[2y];
TanToTrig[(1 + tan[y_]^2)/(2 tan[y_])]:=Csc[2y];
TanToTrig[(1 - tan[y_]^2)/(2 tan[y_])]:= Cot[2y];
TanToTrig[e_]:=e*)
TanToTrig[1+tan[x_]^2]:= Sec[x]^2;
TanToTrig[z_] := Module[{y,numerator,denominator},
	numerator=Numerator[z];
	denominator=Denominator[z];
	If[Head[numerator]==tan,
		y=First[numerator];
		If[denominator==(1+tan[y]^2),
			Return[(1/2) Sin[2y]]]];
	If[Head[numerator/2]==tan,
		y=First[numerator/2];
		If[denominator==(1+tan[y]^2),
			Return[Sin[2y]]]];
	If[(Head[1-numerator]==Power)&&(Head[First[1-numerator]]==tan)&&(Rest[1-numerator]==2),
		y=First[First[1-numerator]];
		If[denominator==(1+tan[y]^2),
			Return[Cos[2y]]]];
	If[(Head[1-denominator]==Power)&&(Head[First[1-denominator]]==tan)&&(Rest[1-denominator]==2),
		y=First[First[1-denominator]];
		If[numerator==(1+tan[y]^2),
			Return[Sec[2y]]]];
	If[Head[denominator/2]==tan,
		y=First[denominator/2];
		If[numerator==(1+tan[y]^2),
			Return[Csc[2y]]]];
	If[Head[denominator/2]==tan,
		y=First[denominator/2];
		If[numerator==(1-tan[y]^2),
			Return[Cot[2y]]]];
	Return[z]]
		

myVariables[e : (_Plus | _Times)] := Union[Flatten[myVariables/@Apply[List, e]]];
myVariables[HoldPattern[Power][e_, a_Integer]] := myVariables[e];
myVariables[e_ /; NumericQ[e]] := {};
myVariables[HoldPattern[Power][x_, p_Plus]] := 
       Union[Flatten[ myVariables[x^Apply[List,p]] ]];
myVariables[e_] := {e};
SetAttributes[myVariables, {Listable}];

PolyCoeffs[p_, vars_] := 
 Block[{t}, 
  Union@Flatten[
    CoefficientArrays[p, vars] /. 
     t_SparseArray :> ArrayRules[t][[All, 2]]] ]

(* This works for polynomials.  At this moment it doesn't have any restriction on it because I will use it 
   specifically for polynomials. This function is not intended to be visible, so I think there is no need to 
   improve it. *)
td[mono_] := Total[ Exponent[ mono, myVariables[mono] ] ];
td[mono_, vars_] := Total[ Exponent[ mono, vars ] ];
totalDeg[poly_Plus] := Max[ td /@ List @@ poly ];
totalDeg[poly_] := td[poly];
totalDeg[poly_Plus, vars_] := Max[ td[#, vars] & /@ List @@ poly ];
totalDeg[poly_, vars_] := td[poly, vars];

(* To detect rational numbers *)
RationalNumberQ[_Rational | _Integer] := True;
RationalNumberQ[___] := False

(* To detect rational functions *)
RationalFunctionQ[expr : (_Plus | _Times), x_] := 
	Fold[Function[{pr, el}, pr && RationalFunctionQ[el, x]], True, List @@ expr];
RationalFunctionQ[HoldPattern[Power][e_, a_Integer], x_] := RationalFunctionQ[e, x];
RationalFunctionQ[x_, x_] := True;
RationalFunctionQ[expr : Except[_Times | _Plus], x_List] := Fold[#1 && (expr === #2 || FreeQ[expr, #2]) &, True, x];
RationalFunctionQ[expr : Except[_Times | _Plus], x : Except[_List]] := FreeQ[expr, x];

(* To delete column of index 'index' of a matrix M *)
DeleteColumn[matrix_, index_] := Delete[#, index] & /@ matrix;

BlockJoin[ A_, B_] := Module[{dima = Dimensions[A], dimb = Dimensions[B], const,  b = B},
  const = ConstantArray[0, {First[dimb], Last[dima]}];
  b = Join[const, b, 2];
  PadRight[ Join[A, b ]]
]

RandomMatrix[rows_, columns_, range_] := Table[RandomChoice[Join[Range[0, range], -Range[range]], columns], {i, rows}]

ZeroColumnQ[mx_, index_] := If[mx[[All, index]] === ConstantArray[0, Length[mx] ], True, False];

Clear[PaddedSparseJoin];

PaddedSparseJoin[a_List, b_List,level_:1] := PadRight[Join[a, b, level]]

PaddedSparseJoin[a_SparseArray, b_List, level_:1] := 
 With[{dima = Dimensions[a], dimb = Dimensions[b]}, 
  With[{d = Max[dima[[-level]], dimb[[-level]]]},
   Join[SparseArray[ArrayRules[a], ReplacePart[dima, -level -> d]], 
    SparseArray[b, ReplacePart[dimb, -level -> d]], level]
   ]]

PaddedSparseJoin[b_List, a_SparseArray, level_:1] := 
 With[{dima = Dimensions[a], dimb = Dimensions[b]}, 
  With[{d = Max[dima[[-level]], dimb[[-level]]]},
   Join[SparseArray[ArrayRules[b], ReplacePart[dimb, -level -> d]], 
    SparseArray[a, ReplacePart[dima, -level -> d]], level]
   ]]

PaddedSparseJoin[a_SparseArray, b_SparseArray, level_:1] := 
 With[{dima = Dimensions[a], dimb = Dimensions[b]}, 
  With[{d = Max[dima[[-level]], dimb[[-level]] ]},
   Join[SparseArray[ArrayRules[a], ReplacePart[dima, -level -> d]], 
    SparseArray[ArrayRules[b], ReplacePart[dimb, -level -> d]], level]
   ]]
   
(*PaddedSparseJoin[a_,b_,level_:1] := (
 If[!FreeQ[{a,b,level},Join,Heads->True],
 	Print["Faulty arguments ", {a,b,level}];
 	1/0;
 ];
 1 /; False)
*)
(* To put together the logs.  This will be used in recognition of (Radical) Log Derivatives. *)
CLog[a_ Log[b_]] := Log[b^a];
CLog[c_Plus] := With[{logfree = DeleteCases[c, a_. Log[b_]]}, 
	 logfree + 
	    With[{e2 = (c - logfree)},
	 		If[ Head[e2] === Plus, Log[Times @@ Cases[e2,a_. Log[b_] :> b^a] ], 
	 			CLog[e2] 
	 		]
	 	]
];
CLog[x_]:=x;
CollectLog[exp_] := CLog[ Expand[exp, Log] ]

(* To do Re[x+I y] = x instead of -Im[y]+Re[x] *)
myRe[expr_] := ComplexExpand[ Re[expr] ];
 
myIm[expr_] := ComplexExpand[ Im[expr] ];

(* To extract the first vector with the first entry non-zero.*)
FirstWithNonZeroFirstEntry[c_List, theT_] := 
 Extract[c, Flatten[ Position[ c, {x_,___} /; NonZeroPolynomialQ[x, theT], {1}, 1 ] ] ];


(* To extract the first vector with the first two entries non-zero.*)
FirstWithNonZeroFirstTwoEntries[c_List, theT_] := 
 Extract[c, Flatten[ Position[ c, {x_,y_, ___} /; NonZeroPolynomialQ[x, theT] && 
 			NonZeroPolynomialQ[y, theT], {1}, 1 ] ] ];

(* To extract the first vector with the first entry 0 and second entry non-zero.*)
FirstWithZeroFirstEntryAndNonZeroSecond[c_List, theT_] := 
 Extract[c, Flatten[ Position[ c, {0,y_, ___} /;  NonZeroPolynomialQ[y, theT], {1}, 1 ] ] ];

RationalMultipleCoefficients[p_, q_, x_, n_, m_]/;
(PolynomialQ[p, x] && PolynomialQ[q, x] && IntegerQ[n] && IntegerQ[m] && n>=0 && m>=0):= 
Module[{clp, clq, zeroclp, zeroclq, list},
(* Return a non-zero rational number r such that the coefficients of t^i, i = n,..,m in q are the same as those of 
   p times r, otherwise returns $Failed.
   
   Example: p = 1 + 7 x + 3 x^2 + 4 x^3 and
			q = 2/3 + (14/3)x + 2 x^2 + (8/3) x^3 
   then RationalMultipleCoefficients[p,q,x,1,3] returns 3/2 i.e. {3, 4} = (3/2){2, 8/3} *)
  	{clp, clq} = Table[ {Coefficient[#, x, i], i}, {i, n , m} ] & /@ {p, q};
  	{zeroclp, zeroclq} = Cases[#, {0, _}] & /@ {clp, clq};
  	If[zeroclp === zeroclq,
  		{clp, clq} = First /@ DeleteCases[#, {0, _}] & /@ {clp, clq};
   		list = clp/clq // Union;
   		If[ Length[list] == 1 && RationalNumberQ[First[list]],
    		First[list],
    	(*Else*)
    		NoSolution
    	],
  	(*Else*)
   		NoSolution
   	]
]

(* Returns the linear factors of 'p' as a polynomial in 'z' *)
PolynomialLinearFactors[p_,z_]:=Module[{pp},
	pp = PolyPP[p, z];
	If[ ! ArrayQ[ Algebra`Polynomial`NestedTermsList[pp, z][[All, -1]], 1, IntegerQ], 
		Return[{}]
	];
	pp = FactorList[pp][[All,1]];
	If[ Max[ Exponent[pp, z] ] > 1, Return[{}] ];
	Select[ pp, Exponent[#, z] == 1& ]
]

(* Returns the integer roots of a polynomial 'p' in 'z'. *)
IntegerRootsPolynomialQ[p_, z_] := With[{pp = PolynomialLinearFactors[p,z]},
	pp =!= {} && ArrayQ[ lc[#, z]& /@ pp, 1, (#^2 == 1 &) ]
]

(* Returns the rational roots of a polynomial 'p' in 'z'. *)
RationalRootsPolynomialQ[p_, z_] := With[{pp=PolynomialLinearFactors[p,z]},
	pp =!= {} && ArrayQ[ lc[#,z]& /@ pp, 1, IntegerQ ]
]


(*======= RECOGNIZING THE MONOMIALS EXTENSIONS =======================*)
PrimitiveMonomialQ[lv_List, ld_List] := lv =!= {} && FreeQ[Last[ld],Last[lv]];
PrimitiveMonomialQ[_,{}] := False

HyperExponentialMonomialQ[lv_List, ld_List] := lv =!= {} && 
 With[{x = Last[lv], ht = Last[ld]}, 
  	PolynomialQ[ht, x] &&  Exponent[ht, x] == 1 &&
  	ZeroPolynomialQ[PolynomialRemainder[ht, x, x], x] ]
HyperExponentialMonomialQ[_,{}] := False

HyperTangentMonomialQ[lv_List, ld_List] := lv =!= {} && 
 With[{x=Last[lv], ht=Last[ld]}, 
  	PolynomialQ[ht, x] &&  Exponent[ht, x] == 2 &&
  	ZeroPolynomialQ[PolynomialRemainder[ht, (1 + x^2), x], x] ]
HyperTangentMonomialQ[_,{}] := False  	

(*====================================================================*)

(*======= RECOGNIZING NORMAL AND SPECIAL ELEMENTS ====================*)
SpecialElementQ[p_, lv_List, ld_List]/;PolynomialQ[ p, Last[lv] ]:= With[{Dp = Derivation[lv, ld][p], t = Last[lv]},
	ZeroPolynomialQ[PolynomialRemainder[Dp, p, t], t]
]

NormalElementQ[p_, lv_List, ld_List]/;PolynomialQ[ p, Last[lv] ]:= With[{Dp = Derivation[lv, ld][p], t = Last[lv]},
	FreeQ[ PolynomialGCD[p, Dp], t ]
]

ReduceElementQ[r_, lv_, ld_]/;RationalFunctionQ[ r, Last[lv] ]:= SpecialElementQ[ Denominator[ Together[r] ], lv, ld ];

SimpleElementQ[r_, lv_, ld_]/;RationalFunctionQ[ r, Last[lv] ]:= NormalElementQ[ Denominator[ Together[r] ], lv, ld ];
(*====================================================================*)

(*=================== RECOGNIZING LOG DERIVATIVES AND LOG DERIVATIVES OF k (t)-RADICALS =====================*)
(********* Auxilary Functions for recognition of Log Derivatives and of Radical Log Derivatives   ***********)

ToCollectLog[expr_]:= With[{toCheck = CollectLog[expr]},
	If[Head[toCheck] === Log,
		First[toCheck],
		toCheck
	]
]; 

(* Primitive Case for Log Derivatives*)
PolynomialLogDerivativeTest[p_,lv_List,ld_List,TheLog_]/;PrimitiveMonomialQ[lv,ld]:=
(* NOTE:  This function has very specific entries and scope.  It is intended to be used by LogarithmicDerivativeQ 
          and NOT to be visible to the user. For that reason it doesn't have conditionals that check that 
		  the entries are valid. 
*)
Module[{LV, LD, theT, intN, theV},
	theT = Last[lv];
	If[Exponent[p, theT] >= 1,
		Return[ {False, NoSolution} ]
	];
	If[ZeroPolynomialQ[p, theT],
		Return[ { True, First[CollectLog[TheLog]]//Quiet} ]
	];
	{LV, LD} = Most /@ {lv, ld};
	If[LV === {},
		Return[ {False, NoSolution} ],
		LogarithmicDerivativeQ[p, LV, LD, TheLog]
	]
]

(* HyperTangent Case for Log Derivatives*)
PolynomialLogDerivativeTest[p_,lv_,ld_,TheLog_]/;HyperTangentMonomialQ[lv,ld]:=
(* NOTE:  This function has very specific entries and scope.  It is intended to be used by LogarithmicDerivativeQ 
          and NOT to be visible to the user. For that reason it doesn't have conditionals that check that 
		  the entries are valid. 
*)
Module[{LV, LD, theT, a, b, intN, theV},
	theT = Last[lv];
	If[Exponent[p, theT]>=2,
		Return[ {False, NoSolution} ]
	];
	If[ZeroPolynomialQ[p,theT],
		Return[ { True, First[CollectLog[TheLog]]//Quiet} ]
	];
	{a, b} = Coefficient[p,theT,#]& /@ {0, 1};
	If[!IntegerQ[ (b/2) PolynomialQuotient[ 1 + theT^2,Last[ld],theT ] ],
		Return[ {False, NoSolution} ]
	];
	{LV, LD} = Most /@ {lv, ld};
	If[LV === {},
		Return[ {False, NoSolution} ],
		LogarithmicDerivativeQ[a, LV, LD, TheLog]
	]
]

(* HyperExponential Case for Log Derivatives*)
PolynomialLogDerivativeTest[p_,lv_,ld_,TheLog_]/;HyperExponentialMonomialQ[lv,ld]:=
(* NOTE:  This function has very specific entries and scope.  It is intended to be used by LogarithmicDerivativeQ 
          and NOT to be visible to the user. For that reason it doesn't have conditionals that check that 
		  the entries are valid. 
*)
Module[{theT, e, v, list, n, theLog },
	theT = Last[lv];
	If[ZeroPolynomialQ[p, theT],
		Return[ {True, First[CollectLog[TheLog]]//Quiet} ]
	];
	If[!FreeQ[p, theT],
		Return[ {False, NoSolution} ]
	];
	list = ParametricLogarithmicDerivative[ p, theT, Last[ld], Most[lv], Most[ld] ];
	If[First[list] === $Failed,
		Return[ {False, NoSolution} ]
	];
	{n, e, v} = list;
	If[n === 1,
		theLog = TheLog + e*Log[v];
		Return[ { True, First[CollectLog[TheLog]]//Quiet } ]
	];
]

(* Primitive Case for Radical Log Derivatives*)
PolynomialRadicalLogDerivativeTest[p_,lv_List,ld_List,TheLog_]/;PrimitiveMonomialQ[lv,ld]:=
(* NOTE:  This function has very specific entries and scope.  It is intended to be used by 
		  RadicalLogarithmicDerivativeQ and NOT to be visible to the user. For that reason it doesn't 
		  have conditionals that check that the entries are valid. 
*)
Module[{LV, LD, theT, intN, theV},
	theT = Last[lv];
	If[Exponent[p, theT] >= 1,
		Return[ {False, NoSolution, NoSolution} ]
	];
	If[ZeroPolynomialQ[p,theT],
		{theV, intN} = NumeratorDenominator[TheLog];
		(*Return[ { True, First[ToCollectLog[TheLog] ], TheLog } ]*)
		Return[{ True, intN, First[CollectLog[theV]]//Quiet }]
	];
	{LV, LD} = Most /@ {lv, ld};
	If[LV === {},
		Return[ {False, NoSolution, NoSolution} ],
		RadicalLogarithmicDerivativeQ[p, LV, LD, TheLog]
	]
]

(* HyperTangent Case for Radical Log Derivatives*)
PolynomialRadicalLogDerivativeTest[p_,lv_,ld_,TheLog_]/;HyperTangentMonomialQ[lv,ld]:=
(* NOTE:  This function has very specific entries and scope.  It is intended to be used by 
		  RadicalLogarithmicDerivativeQ and NOT to be visible to the user. For that reason it doesn't 
		  have conditionals that check that the entries are valid. 
*)
Module[{LV, LD, theT, a, b, intN , theV},
	theT = Last[lv];
	If[Exponent[p, theT] >= 2,
		Return[ {False, NoSolution, NoSolution} ]
	];
	If[ZeroPolynomialQ[p,theT],
		{theV, intN} = NumeratorDenominator[TheLog];
		(*Return[ { True, First[ToCollectLog[TheLog] ], TheLog } ]*)
		Return[{ True, intN, First[CollectLog[theV]]//Quiet }]
	];
	{a, b} = Coefficient[p, theT, #]& /@ {0, 1};
	If[!IntegerQ[ (b/2) PolynomialQuotient[1 + theT^2, Last[ld], theT] ],
		Return[ {False, NoSolution, NoSolution} ]
	];
	{LV, LD} = Most /@ {lv, ld};
	If[LV === {},
		Return[ {False, NoSolution, NoSolution} ],
		RadicalLogarithmicDerivativeQ[a, LV, LD, TheLog]
	]
]

(* HyperExponential Case for Log Derivatives*)
PolynomialRadicalLogDerivativeTest[p_,lv_,ld_,TheLog_]/;HyperExponentialMonomialQ[lv,ld]:=
(* NOTE:  This function has very specific entries and scope.  It is intended to be used by RadicalLogarithmicDerivativeQ 
          and NOT to be visible to the user. For that reason it doesn't have conditionals that check that 
		  the entries are valid. 
*)
Module[{theT, e, v, list, n, theLog },
	theT = Last[lv];
	If[ZeroPolynomialQ[p, theT],
		{theV, intN} = NumeratorDenominator[TheLog];
		(*Return[ { True, First[ToCollectLog[TheLog] ], TheLog } ]*)
		Return[{ True, intN, First[CollectLog[theV]]//Quiet }]
	];
	If[!FreeQ[p, theT],
		Return[ {False, NoSolution, NoSolution} ]
	];
	list = ParametricLogarithmicDerivative[ p, theT, Last[ld], Most[lv], Most[ld] ];
	If[First[list] === $Failed,
		Return[ {False, NoSolution, NoSolution} ]
	];
	{n, e, v} = list;
	theLog = TheLog + e*Log[v];
	Return[ { True, n, First[CollectLog[ theLog]]//Quiet  } ]

]


(***** End of Auxilary Functions for recognition of Log Derivatives and of Radical Log Derivatives   ******)

(* Recognition of Logarithmic Derivatives *)

(* If the last two entries are empty, then we are in the constant field (call it C).  So, D (c) = 0 for every element 
   and therefore if f !=0 then it cannot be a logarithimic derivative of an element in C.  Also, since we know that 
   D (1) = 0 always (doesn't matter what type of derivation we have) then it is safe to assume the following.  *)
LogarithmicDerivativeQ[f_, {}, {}]:= If[f === 0,
	{True, 1},
	{False, NoSolution}
];

LogarithmicDerivativeQ[f_,lv_List,ld_List,theLog_:0]:=
 Module[{r, p, a, d, g, theT, DD, z, TheLog},
	theT = Last[lv];
	If[ZeroPolynomialQ[f, theT],
		Return[ {False, NoSolution}]
	];
	DD = Derivation[lv,ld];
	{a, d} = NumeratorDenominator[f];
	If[!FreeQ[ PolynomialGCD[ d, DD[d] ], theT ],
		Return[ {False, NoSolution} ]
	];
	r = Resultant[ a - z DD[d], d, theT ];
	If[ IntegerRootsPolynomialQ[r, z], 
			g = First[ ResidueReduce[f, lv, ld] ] , 
			g = 0
	];
	TheLog = theLog + g;
	p = f - DD[g] //Together;
	If[!PolynomialQ[p, theT],
		Return[ {False, NoSolution} ]
	];
	PolynomialLogDerivativeTest[p, lv, ld, TheLog]
]

(* If the last two entries are empty, then we are in the constant field (call it C).  So, D (c) = 0 for every element 
   and therefore if f !=0 then it cannot be a logarithimic derivative of C - radical.  Also, since we know that 
   D (1) = 0 always (doesn't matter what type of derivation we have) then it is safe to assume the following.  *)
RadicalLogarithmicDerivativeQ[f_, {}, {}]:= If[f === 0,
	{True, 1, 1},
	{False, NoSolution, NoSolution}
];

(* Recognition of Log Derivatives for k (t)-radicals *)
RadicalLogarithmicDerivativeQ[f_,lv_List,ld_List,theLog_:0] := 
Module[{r, p, a, d, rootList, g, theT, DD, z, TheLog},
	theT = Last[lv];
	If[ZeroPolynomialQ[f, theT],
		Return[ {False, NoSolution, NoSolution}]
	];
	DD = Derivation[lv, ld];
	{a, d} = NumeratorDenominator[f];
	If[!FreeQ[ PolynomialGCD[ d, DD[d] ],theT ],
		Return[ {False, NoSolution, NoSolution} ]
	];
	r = Resultant[ a - z DD[d], d, theT ];
	If[ RationalRootsPolynomialQ[r, z], 
			g = First[ResidueReduce[f, lv, ld] ] , 
			g = 0
	];
	TheLog = theLog + g;
	p = f - DD[g] //Together;
	If[!PolynomialQ[p, theT],
		Return[ {False, NoSolution, NoSolution} ]
	];
	PolynomialRadicalLogDerivativeTest[p, lv, ld, TheLog]
]

(*======= End of Recognizing Log Derivatives and Log Derivatives of k (t)-radicals ===========*)


(*================== RECOGNIZING DERIVATIVES ==========================*)
(********* Auxilary Functions for recognition of derivatives   ***********)
(* primitve and hyperexponential case *) 
FirstDerivativeTest[p_,lv_,ld_]/;(PrimitiveMonomialQ[lv,ld] || HyperExponentialMonomialQ[lv,ld]):= 
IntegratePolynomial[p, lv, ld];

(* hypertangent case *)

FirstDerivativeTest[p_,lv_,ld_]/;HyperTangentMonomialQ[lv, ld]:= 
Module[{pp, q1, beta, theT = Last[lv], DD = Derivation[lv, ld], c},
	{q1, beta} = IntegrateHypertangentReduced[p, lv, ld];
	If[beta == 0,
		Return[NoSolution]
	];
	pp = p - DD[q1] //Together;
	{q1, c} =  IntegratePolynomial[pp, lv, ld];
	pp = pp - DD[q1] - c DD[theT^2+1]/(theT^2+1) //Together;
	If[ ZeroPolynomialQ[DD[c], theT],
		beta = 1,
		beta = 0
	];
	{pp, beta}
];

(* primitive case *)
SecondDerivativeTest[a_, lv_, ld_,g_, q_]/;PrimitiveMonomialQ[lv, ld]:= Module[{theT, list, v, c},
(* NOTE: This function has very specific entries and scope.  It is intended to be used by DerivativeQ and not by
         the users.  *)
	theT = Last[lv];
	list = LimitedIntegrate[a, {Last[ld]}, Most[lv], Most[ld] ];
	If[ list === NoSolution,
		Return[ {False, NoSolution} ]
	];
	{v , {c}} = list;
	{True, g + q + v + c*theT // Together}
]

(* when deg (Dt) >= 1 *)
SecondDerivativeTest[a_, lv_, ld_,g_, q_]/;(Exponent[ Last[ld], Last[lv] ] > 0):= DerivativeQ[a, Most[lv], Most[ld], g, q];

(******* End of Auxilary Functions for recognition of derivatives *******)

(* Recognize Derivatives t is primitive or hyperexponential *)

(* If the last two entries are empty, then we are in the constant field (call it C).  So, D (c) = 0 for every element 
   and therefore if f !=0 then it cannot be a derivative of an element in C.  Also, since we know that D (1) = 0 always
   (doesn't matter what type of derivation we have) then it is safe to assume the following.  *)
DerivativeQ[f_, {}, {} ]:= If[f === 0, {True, 1}, {False, NoSolution}]

DerivativeQ[f_, lv_List, ld_List, g1_:0, q1_:0 ]/;(PrimitiveMonomialQ[lv, ld] || HyperExponentialMonomialQ[lv, ld] || HyperTangentMonomialQ[lv, ld]):=
(* This function uses IntegratePolynomial which, as of today, is only implemented for Primitive monomials. *)
Module[{g, h, r, p, beta, q, a, list, v, c, theT, DD, q2, g2, qq1},
	If[!RationalFunctionQ[f,lv],
		Return[ {False, NoSolution}]
	];
	theT = Last[lv];
	DD = Derivation[lv, ld];
	{g2, h, r} = MonomialHermiteReduce[f, lv, ld]//Together; (* f = Dg + h + r, h simple and r reduce *)
	g = g1 + g2;
	If[!PolynomialQ[h, theT],       
		Return[ {False, NoSolution} ]
	];	
	p = h + r; (* At this stage h + r is a reduced element, since r is reduce and h a polynomial. *)
	{q2, beta} = FirstDerivativeTest[p, lv, ld]; (* p - Dq in k. *)
	If[beta === 0,
		Return[ {False, NoSolution} ]
	];
	q = q1 + q2;
	a = p - DD[q2] //Together;
	SecondDerivativeTest[a, lv, ld, g, q]
]
(*================== End of Recognizing of Derivatives =======================*)

(*======= RECOGNIZING IF IRREDUCIBLE SPECIALS ARE OF THE FIRST KIND ==========*)	

(* Primitive Case *)
IrrSpecialsAreOfFirstKindQ[lv_, ld_] /;PrimitiveMonomialQ[lv, ld] := True;

(* HyperExponential Case*)
IrrSpecialsAreOfFirstKindQ[lv_, ld_] /;HyperExponentialMonomialQ[lv, ld] :=
(* In the HyperExponential case i.e. D[t] = a*t for a in k, we have Sirr = {t}.  Since the only root of t is alpha=0,
   then p_alpha[t] = (D[t]-D[alpha])/(t - alpha) = a*t/t = a.  So we only need to check that D[t]/t is not a 
   logarithimic derivative of k-radicals. 
   
   NOTE:  We need to implement RadicalLogarithmicDerivativeQ for Hyper Exponential Monomials *)
  Not[ First[ RadicalLogarithmicDerivativeQ[ Together[ Last[ld]/Last[lv] ], Most[lv], Most[ld] ] ] ];

IrrSpecialsAreOfFirstKindQ[lv_, ld_] /;HyperTangentMonomialQ[lv, ld] := 
(* In the HyperTangent case i.e. D[t] = a (t^2+1) for a in k, we have (assuming I = Sqrt[-1] not in k) Sirr = {t^2+1}.  
   Since the only roots of t^2+1 are alpha (+-) = (+-)I, then p_alpha (+-)[t] = (D[t]-D[alpha])/(t - alpha) = 
   a (t^2+1)/(t -+ I) = +- 2aI. So we only need to check that 2I (D[t]/(t^2+1)) = 2aI is not a logarithimic derivative 
   of a k (I)-radicals. *)
Module[{toCheck, a},
  	a = Together[Last[ld]/(Last[lv]^2 + 1)];
  	toCheck =  RadicalLogarithmicDerivativeQ[2 a I, Most[lv], Most[ld] ];
  	Not[ First[toCheck] ]
]
