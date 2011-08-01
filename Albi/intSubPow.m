(* ::Package:: *)

(* Method 2 in Stage II, (2)integral powers of variables  *)
(*The integrand is of the form x^c Elem (x^Subscript[k, i]),where c,Subscript[k, i] are integers
substitute y=x^k,k=gcd ({c+1,Subscript[k, 1],Subscript[k, 2],...}),k!=1,returns the transformed integrand*)
intSubPow[f_,x_]:=Module[
	{e=f,pos,c,temp,i,m={},pow,ki,k,exponent},
	If[Head[e]===Times,
		temp=Level[e,1][[1]],
		Return["NotMatch"]
	];

	If[MatchQ[temp,x^_],(*the first part is of the form x^c*)
		exponent=Level[temp,1][[2]];
		If[!IntegerQ[exponent],
			If[Head[exponent]===Times&&FreeQ[exponent,x],
				If[!IntegerQ[c=Level[exponent,1][[1]]],
					Return["NotMatch"]
				];
				exponent=exponent/c,
				Return["NotMatch"]
			],
			c=exponent;
			exponent=1
		];
		temp=e/temp,	
(* the following part seems to be wrong, bucause here e/temp is still part1
  besides, why counld part 2 be also the form x^c? 		
		If[MatchQ[e/temp,x^_],(*the second part is of the form x^c,c!=1*)
			exponent=Level[e/temp,1][[2]];
			If[!IntegerQ[exponent],
				If[Head[exponent]===Times&&FreeQ[exponent,x],
					If[!IntegerQ[c=Level[exponent,1][[1]]],
						Return["NotMatch"]
					];
					exponent=exponent/c,
					Return["NotMatch"]
				],
				c=exponent;
				exponent=1
			],
			Return["NotMatch"]
		]
*)


	];
	(*Now temp is of the form Elem (x^Subscript[k, i])*)
	AppendTo[m,c+1];
	pos=Position[temp,Power[x,_]];
	If[pos=={},
		Return["NotMatch"]
	];
	Do[
		pow=Extract[temp,pos[[i]]];
		ki=Level[pow,1][[2]];
		If[!IntegerQ[ki=ki/exponent],
			Return["NotMatch"]
		];		
		AppendTo[m,ki],
		{i,Length[pos]}
	];
	k=Apply[GCD,m];
	e=e/(k*exponent*x^(k*exponent-1));
	e=e/.x->y^(1/(k*exponent));
	Return[{Simplify[e],y,x^(k*exponent)}]	
]
(*Note1:Unlike FORM,this method obtain a clue which determines whether this transformation is applicable;and this transformation is called when none of the other methods is applicable*)
(*Note2:Now it is extended to handle exponents such as 3a,2a in Integrate[x^(3a)Sin[x^(2a)],x]*)
(* Attention: the extention in Note2 seems unnecessary, this part of work should be reexamined
 notice that expr like (y^(1/(2 a)))^(2 a) cannot be simplified, so it's hard for following programs
to deal with*)


  


intSubPow[Sin[x^2]*x^3,x]
intSubPow[x^7/(x^12+1),x]
intSubPow[x^(3a)Sin[x^(2a)],x]
intSubPow[x^(7a)/(x^(12a)+1)*Sin[x],x]













