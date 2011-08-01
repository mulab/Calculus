(* ::Package:: *)

(*The integrand is of the form x^c Elem (x^Subscript[k, i]),where c,Subscript[k, i] are integers
substitute y=x^k,k=gcd ({c+1,Subscript[k, 1],Subscript[k, 2],...}),k!=1,returns the transformed integrand*)
intSubPow[f_,x_]:=Module[
	{e=f,pos,c,temp,i,m={},pow,ki,k,exponent},
	If[Head[e]===Times,
		temp=Level[e,1][[1]],
		Return[A[f,x]]
	];
	If[MatchQ[temp,x^_],(*the first part is of the form x^c*)
		exponent=Level[temp,1][[2]];
		If[!IntegerQ[exponent],
			If[Head[exponent]===Times&&FreeQ[exponent,x],
				If[!IntegerQ[c=Level[exponent,1][[1]]],
					Return[A[f,x]]
				];
				exponent=exponent/c,
				Return[A[f,x]]
			],
			c=exponent;
			exponent=1
		];
		temp=e/temp,			
		If[MatchQ[e/temp,x^_],(*the second part is of the form x^c,c!=1*)
			exponent=Level[e/temp,1][[2]];
			If[!IntegerQ[exponent],
				If[Head[exponent]===Times&&FreeQ[exponent,x],
					If[!IntegerQ[c=Level[exponent,1][[1]]],
						Return[A[f,x]]
					];
					exponent=exponent/c,
					Return[A[f,x]]
				],
				c=exponent;
				exponent=1
			],
			Return[A[f,x]]
		]
	];
	(*Now temp is of the form Elem (x^Subscript[k, i])*)
	AppendTo[m,c+1];
	pos=Position[temp,Power[x,_]];
	If[pos=={},
		Return[A[f,x]]
	];
	Do[
		pow=Extract[temp,pos[[i]]];
		ki=Level[pow,1][[2]];
		If[!IntegerQ[ki=ki/exponent],
			Return[A[f,x]]
		];		
		AppendTo[m,ki],
		{i,Length[pos]}
	];
	k=Apply[GCD,m];
	e=e/(k*exponent*x^(k*exponent-1));
	e=e/.x->y^(1/(k*exponent));
	Return[Simplify[e]]	
]
(*Note1:Unlike FORM,this method obtain a clue which determines whether this transformation is applicable;and this transformation is called when none of the other methods is applicable*)
(*Note2:Now it is extended to handle exponents such as 3a,2a in Integrate[x^(3a)Sin[x^(2a)],x]*)


(*Test:
intSubPow[x^3Sin[x^2],x]
intSubPow[x^7/(x^12+1),x]
intSubPow[x^(3a)Sin[x^(2a)],x]
intSubPow[x^(7a)/(x^(12a)+1),x]
*)



