(* ::Package:: *)

(*The integrand is of the form x^c Elem (x^Subscript[k, i]),where c,Subscript[k, i] are integers
substitute y=x^k,k=gcd ({c+1,Subscript[k, 1],Subscript[k, 2],...}),k!=1,returns the transformed integrand*)
intSubPow[f_,x_]:=Module[
	{e=f,pos,c,temp,i,m={},pow,ki,k,y},
	If[Head[e]===Times,
		temp=Level[e,1][[1]],
		Return["NotMatch"]
	];
	If[MatchQ[temp,x^_Integer],(*the first part is of the form x^c*)
		c=Level[temp,1][[2]];
		temp=e/temp,
		If[MatchQ[e/temp,x^_Integer],(*the second part is of the form x^c,c!=1*)
			c=Level[e/temp,1][[2]],
			Return["NotMatch"]
		]
	];
	(*Now temp is of the form Elem (x^Subscript[k, i])*)
	AppendTo[m,c+1];
	pos=Position[temp,Power[x,_Integer]];
	If[pos=={},
		Return["NotMatch"]
	];
	Do[
		pow=Extract[temp,pos[[i]]];
		ki=Level[pow,1][[2]];
		AppendTo[m,ki],
		{i,Length[pos]}
	];
	k=Apply[GCD,m];
	If[k==1,
		Return["NotMatch"]
	];
	e=e/(k*x^(k-1));
	e=e/.x->y^(1/k);
	Return[{e,y,x^k}]	
]
(*Note:Unlike FORM,this method obtain a clue which determines whether this transformation is applicable;and this transformation is called when none of the other methods is applicable*)


(*Test:
intSubPow[x^3Sin[x^2],x]
intSubPow[x^7/(x^12+1),x]
*)
