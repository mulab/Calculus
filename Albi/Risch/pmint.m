(* ::Package:: *)

(* ::Text:: *)
(*Parallel Risch*)
(*Authors: Luis A. Medina and Sasha Pavlyk                    *)
(*Mathematica Version: 6.0*)
(**)
(*This is a Mathematica implementation of Manuel Bronstein's Poor Man Integrator available at*)
(**)
(*http://www-sop.inria.fr/cafe/Manuel.Bronstein/pmint/index.html*)
(**)
(*Please report bug to:  lmedina at math dot rutgers dot edu.*)
(**)
(*Created: Summer 2007.*)


<<Misc.m
<<AlgebraicPrelim.m
<<RationalIntegration.m


Mensaje::usage="Created: Summer 2007.

This package was written by Luis A. Medina and  Sasha Pavlyk.

This is a \!\(\*
StyleBox[\"Mathematica\",\nFontSlant->\"Italic\"]\) implementation of Manuel Bronstein's 
\!\(\*
StyleBox[\"Poor\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"Man\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"Integrator\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)available at

http://www-sop.inria.fr/cafe/Manuel.Bronstein/pmint/index.html

Please report bug to:  lmedina at math dot rutgers dot edu.

Functions included in this package are:

pmint[f,x]

If you want to know more information about these functions, 
simpliy input ?nameoffunction.  For example, try ?pmint."



pmint::usage="pmint[f,x]: Implementation of the Parallel Risch integration.  This program is based on Manuel Bronstein's \!\(\*
StyleBox[\"Poor\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"Man\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\" \",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\"Integrator\",\nFontSlant->\"Italic\"]\)\!\(\*
StyleBox[\".\",\nFontSlant->\"Italic\"]\)"; 


(*======================= Auxiliary Functions ======================= *)
Derivative[1][exp] = exp;
exp[a_ + b_ ]:= exp[a] exp[b]; 
exp[Log[x_]]:= x;

candidateTower[f_,x_,t_] :=Module[{vars, terms, deriv, newF, limitList, list, F, dterms, count = 0},
(* F is the integrand, x is the variable of integration and t is a dummy
   variable whose use is to name the "new variables" as t[1], t[2],...
   
   Output:  Returns 
   				1) F in terms of new variables.
   				2) The variables to adjoin in order to calc the integral.  We
   				   need this information when changing back the result in terms of
   				   the original variables.
   				3) The last two elements of the output are of the form 
   				   {x,t[1],t[2],..} and {1,D[t[1]],D[t[2]],..}.  These are needed 
   				   in order to produce the Total Derivation.  *)
	F = f //.{Exp[y_]:> exp[y]};
	terms = Select[ myVariables[F], PolynomialQ[#, x] == False & ];
	dterms = Union[ Select[ Flatten[ myVariables[ D[terms,x] ] ], (PolynomialQ[#, x] == False &) ], terms];  					  
	While[ !SubSet[dterms, terms] && count <=15,
		terms = Union[ terms, dterms ];
  		dterms = Union[ Select[ Flatten[ myVariables[ D[terms,x] ] ], (PolynomialQ[#, x] == False &) ], terms];
  		count = count + 1
	];
	
  	If[count > 15,
  		Return[$Failed]
  	];
  	
  	deriv = D[terms, x];
  	vars = Map[t, Range[ Length[terms] ] ];
  	limitList = Thread[ terms -> vars ];
  	newF = F /. limitList;
  	deriv = deriv /. limitList/.{ HoldPattern[ Power ][ a_, b_Plus ] :> Times @@ ((a^Apply[ List, b ])/.limitList) };
  
  	If[True || Fold[ #1 && RationalFunctionQ[#2, Join[ {x}, vars ] ]&, True, deriv],
  		{newF, terms, Join[{x}, vars], Join[{1}, deriv] },
  	(* Else *)
  	    $Failed
  	]
]//.{exp[y_]:> Exp[y]};


Clear[ToIndetsAndDerivation];
ToIndetsAndDerivation[f_,x_,t_] := Module[{vars, terms, deriv, newF, limitList, list, F, dterms, count = 0},
(* F is the integrand, x is the variable of integration and t is a dummy
   variable whose use is to name the "new variables" as t[1], t[2],...
   
   Output:  Returns 
   				1) F in terms of new variables.
   				2) The variables to adjoin in order to calc the integral.  We
   				   need this information when changing back the result in terms of
   				   the original variables.
   				3) The last two elements of the output are of the form 
   				   {x,t[1],t[2],..} and {1,D[t[1]],D[t[2]],..}.  These are needed 
   				   in order to produce the Total Derivation.  *)
	F = f //.{Exp[y_]:> exp[y]};
	terms = Select[ myVariables[F], PolynomialQ[#, x] == False & ];
	dterms = Union[ Select[ Flatten[ myVariables[ D[terms,x] ] ], (PolynomialQ[#, x] == False &) ], terms];  					  
	While[ !SubSet[dterms, terms] && count <=15,
		terms = Union[ terms, dterms ];
  		dterms = Union[ Select[ Flatten[ myVariables[ D[terms,x] ] ], (PolynomialQ[#, x] == False &) ], terms];
  		count = count + 1
	];
	
  	If[count > 15,
  		Return[$Failed]
  	];
  	
  	deriv = D[terms, x];
  	vars = Map[t, Range[ Length[terms] ] ];
  	limitList = Thread[ terms -> vars ];
  	newF = F /. limitList;
  	deriv = deriv /. limitList/.{ HoldPattern[ Power ][ a_, b_Plus ] :> Times @@ ((a^Apply[ List, b ])/.limitList) };
  
  	If[True || Fold[ #1 && RationalFunctionQ[#2, Join[ {x}, vars ] ]&, True, deriv],
  		{newF, terms, Join[{x}, vars], Join[{1}, deriv] },
  	(* Else *)
  	    $Failed
  	]
]//.{exp[y_]:> Exp[y]};


ToTerms[F_, terms_List, vars_List] := F /. Thread[vars -> terms]

denD[derivations_List]:=
(* Assumptions:  "derivations" are the list of the Derivations of the t[i]'s.
				 This list should be given at the time of call denD.  In
				 particular it takes the last element of ToIndetsAndDerivation[f,x,t]*)
PolynomialLCM@@Denominator[Together[derivations]];
(*================== End of Auxiliary Functions =======================*)


(*======================= Parallel Risch ==============================*)
(*=====================================================================*)
Clear[pmint];

(* This is a version of Parallel Integration. *)
pmint[f_,x_]/;RationalFunctionQ[f,x]:=IntegrateRationalFunction[f,x]

pmint[f_,x_]:=Module[{ff,si,li,lin,lout,q,d,l,lv,ld,ls,fint,lc,t,terms,list},
	ff = Together[ TrigToTan[f] ];
	list = ToIndetsAndDerivation[ff, x, t];	
	If[list==$Failed,
		Return[ INT[f] ]
	];
	{ff, terms, lv, ld} = list;
	q = denD[ld];
	ld = q * ld;
	ls = DeleteCases[ Map[ getSpecial[ #, Thread[ terms -> Rest[lv] ] ] &, terms], Null];
	ToTerms[ pmIntegrate[ ff, lv, ld, q, ls ], terms, Rest[lv] ]/.{ tan -> Tan}
]


(* To get the known Darboux polynomials *)
getSpecial[f_tan, ru_] := { 1 + (f/.ru)^2, False };
getSpecial[f_Tanh, ru_] :=With[{ff = f/.ru}, Sequence @@ {{ 1 + ff, False },{ 1 - ff, False} } ];
getSpecial[f_ProductLog, ru_] := { f/.ru, True };
getSpecial[___] := Null;


pmIntegrate[f_,lv_List,ld_List,q_,ls_:{}]:=
Module[{splq, s, df, spl, cden, dg, x, monomials, cand, lunk, sol, i, AA},
	DRPrint["Visit pmIntegrate."];
	splq = splitFactor[q, lv, ld];
	s = First[splq];
	Scan[ If[ Last[#], s = s*First[#] ] &, ls ];
	x = First[lv];
	df = Denominator[f];
	spl = splitFactor[df, lv, ld];
	cden = s * First[spl] * deflation[ Last[spl], lv, ld];
	dg = 1 + totalDeg[s, lv] + Max[ totalDeg[ Numerator[f], lv ], totalDeg[ Denominator[f],lv ] ];
	(* can we estimate the expected number of monomials ?  *)
	(* we should not attempt solving the linear system if the number of such monomials exceeds 500. -- Sasha *)
	monomials = enumerateMonoms[ lv, dg ];
	DRPrint["	There are ", Length[lv] ," new variables in the integrand and the guess bound for deg is ", dg, 
			" therefore the number of monomials is ", Length[monomials],"." ];			
	
	If[Length[monomials] > 800,
		DRPrint["\n Since the number of monomials is bigger than 800, then 'pmint' failed.  It is possible that the integral is doable,"];
		DRPrint["but it will require to much time.  The bound 800 can be changed to a smaller one"];
		Return[INT[f]]
	];
	cand = Total[ Table[ AA[i]*monomials[[i]], { i, Length[monomials] }] ]/cden;
	lunk = Table[ AA[i],{ i, Length[monomials] } ];
	sol = tryIntegral[f, lv, ld, q, cand, lunk, 
				First[spl], (* normal part of df *)
		        Last[spl],  (* special part of df *)
		        Last[splq], (* special part of q *)
		        ls, 0];
	If[First[sol],
		sol = tryIntegral[ f, lv, ld, q, cand, lunk, First[spl], Last[spl], Last[splq], ls, {I} ]
	];
	If[First[sol],
		INT[f],
		Last[sol]
	]
]


Clear[tryIntegral];
tryIntegral[f_,lv_List,ld_List,q_,cand_,lunk_,l1_,l2_,l3_,ls_,k_]:=
(* In this application the "k" is a variable or variables to adjoint *)
Module[{candlog, p, candidate, i, sol, DD, BB, lu, dens},
	DRPrint["Visit tryIntegral."];
	DD = Derivation[lv,ld];
	candlog = Union[ myFactors[l1, k],myFactors[l2, k],myFactors[l3, k], First/@ ls];
				(* "ls" will come from a list generated by getSpecial.
				   Since elements returned by getSpecial are of the form
				   {poly, bool} then we have to map First in order to get
				   the polys. *)  
	candidate = cand + Total[ Table[ BB[i] Log[ candlog[[i]] ], {i, Length[candlog]} ] ];
	lu = Union[lunk, Table[BB[i], {i, Length[candlog]} ] ];
	(* funky way of avoiding doing big Together *)
	DRPrint["	Applying 'funky way' of Together..."];
	sol = Derivation[lv, Together[ld/q]];
	{sol, dens} = Reap[ Collect[ f - sol[candidate], Alternatives @@ lu, 
		    With[{tmp = Together[#]}, Sow[ Denominator[ tmp ] ]; tmp]& ] ];
	dens = PolynomialLCM @@ Flatten[ dens ];
	DRPrint["	Applying Collect..."];	
	sol = Collect[sol, Alternatives @@ lu, Together[ dens*# ]& ];
	(* sol = Numerator[Together[sol]]; *)
	(* sol = Solve[PolyCoeffs[sol,lv]==0, lu]//Quiet; *)
	sol = DeleteCases[ PolyCoeffs[ sol, lv ], 0 ];
	DRPrint["	Applying Outer..."];	
	dens = Outer[D, sol, lu]; 
	DRPrint["	Solving linear equation with a ", First[Dimensions[dens]]," x ", 
			Last[Dimensions[dens]]," matrix."]; 
	
	sol = Quiet[ LinearSolve[ dens, - sol/.Thread[lu->0] ] ];
	If[ Head[sol] === LinearSolve, sol = {} ];
	If[ sol =!= {}, sol = Thread[lu -> sol] ];
	{sol === {}, (candidate/.sol)/.Thread[lu -> 0]}
]


			
myFactors[p_/;!NumericQ[p],0]:= Drop[ First/@ FactorList[p], 1 ];
myFactors[p_,0]={p};
myFactors[p_/;!NumericQ[p],extension_]:= Drop[ First/@FactorList[p, Extension -> extension], 1 ];
myFactors[p_,extension_]:={p};


enumerateMonoms[ {}, deg_ ]:= {1};
enumerateMonoms[lv_List,deg_] := Module[{i, v = Most[lv]},
(* Calculate all the monomials in variables "lv" such that the TOTAL deg
   is less than or equal to "deg" *)	
	Union[enumerateMonoms[v,deg], 
		Sequence @@ Table[Last[lv]^i*enumerateMonoms[v,deg-i], {i,deg} ] 
	]
]


splitFactor[p_,lv_List,ld_List]:=Module[{theT, c, hn, hs, S, q, qn, qs, DD},
(* Caution: This is similar to the previous SplitFactor, but not the same*)
	(*If[ Fold[ Function[ {pr, el}, pr && FreeQ[p, el] ], True, lv ],
		Return[ {1, p} ] 
	];*)
	theT = mainVar[p, lv];
	If[theT ==$Failed,
		Return[{p,1}]
	];
	DD = Derivation[lv, ld];
	{c,q} = PolyContentPP[p, theT];
	{hn,hs} = splitFactor[c, lv, ld];
	S = PolynomialQuotient[ PolynomialGCD[ q, DD[q] ], PolynomialGCD[ q, D[q,theT] ], theT ];
	If[Exponent[S, theT] == 0,
		Return[{hn p, hs}]
	];
	{qn, qs} = splitFactor[ PolynomialQuotient[q, S, theT], lv, ld];
	{hn qn, S hs qs}
]


(* Calculate the deflation of p with respect to the "new derivation". *)
deflation[p_,lv_List,ld_List]:=Module[{theT, c, q, DD},
	theT = mainVar[p, lv];
	If[theT === $Failed, 
		Return[p]
	];
	DD = Derivation[lv, ld];
	{c,q} = PolyContentPP[p, theT];
	deflation[c, lv, ld] * PolynomialGCD[ q, DD[q, theT ] ] 
] 


?Mensaje;
