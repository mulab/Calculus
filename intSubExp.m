(* ::Package:: *)

(*gives the indefinite integral of elementary function of exponentials by transforming Subscript[a, i]^(Subscript[b, i]x+Subscript[c, i]) into Subscript[a, i]^Subscript[c, i]*Subscript[a, 1]^(Subscript[b, i]x*Log[Subscript[a, 1],Subscript[a, i]]), and then mading the substitution y=Subscript[a, 1]^x*)
intSubExp[f_,x_]:=Module[
	{e=f,pos=Position[f,x],loc={},i,j,len,ptr,mp,a={},b={},c={},u,ans},
	ans=Do[(*enumerate each occrurance of x to get Subscript[a, i], Subscript[b, i], Subscript[c, i] and the location*)
		ptr=pos[[i]];
		j=ptr[[-1]];
		len=Length[ptr];
		If[len==0,(*x is at the root*)
			Return["NotMatch"]
		];
		ptr=Delete[ptr,-1];
		If[Head[Extract[e,ptr]]===Times,(*the coefficient of x is not 1*)
			If[len<2,(*the expression f is of the form b*x*)
				Return["NotMatch"]
			];
			mp=Extract[e,ptr];(*main part: b*x*)
			AppendTo[b,mp/x];
			If[!FreeQ[b[[-1]],x],
				Return["NotMatch"]
			];
			j=ptr[[-1]];
			ptr=Delete[ptr,-1],
			(*is 1*)
			AppendTo[b,1];
			mp=x
		];
		If[Head[Extract[e,ptr]]===Plus,(*the const c is not 0*)
			If[len<3,(*the expression f is of the form b*x+c*)
				Return["NotMatch"]
			];
			AppendTo[c,Extract[e,ptr]-mp];
			If[!FreeQ[c[[-1]],x],
				Return["NotMatch"]
			];
			j=ptr[[-1]];
			ptr=Delete[ptr,-1],
			(*is 0*)
			AppendTo[c,0]
		];
		If[Head[Extract[e,{ptr}][[1]]]=!=Power||j!=2(*b*x+c is not the second part*),
			Return["NotMatch"]
		];
		AppendTo[a,Extract[e,Append[ptr,1]]];
		If[!FreeQ[a[[i]],x],
			Return["NotMatch"]
		];
		AppendTo[loc,ptr],
		{i,Length[pos]}
	];
	If[ans!=Null,
		Return[ans]
	];
	Do[(*construct the rule list*)
		loc[[i]]=Rule[loc[[i]],a[[i]]^c[[i]]*u^(b[[i]]*Log[a[[1]],a[[i]]])],
		{i,Length[pos]}
	];
	If[Length[loc]==1&&loc[[1,1]]=={},(*ReplacePart can't deal with the rule like {{}->u}*)
		e=u,
		e=ReplacePart[e,loc]
	];
	e=e/(u*Log[a[[1]]]);
	Return[{e,u,a[[1]]^x}/.u->y]

	(*Return[Integrate[e,u]/.u->a[[1]]^x]*)
	(*{e=f,pos,a,b,c,rule={},u},
	pos=Position[f,(a_Integer|a_Real|a_Rational|a_Complex)^((b_Integer|b_Real|b_Rational|b_Complex)x+(c_Integer|c_Real|c_Rational|c_Complex))];
	{a,b,c}=Cases[f,(a_Integer|a_Real|a_Rational|a_Complex)^((b_Integer|b_Real|b_Rational|b_Complex)x+(c_Integer|c_Real|c_Rational|c_Complex))->{a,b,c}];
	Do[
		AppendTo[rule,pos[[i]]->a[[i]]^c[[i]]*u^(b[[i]]*Log[a[[1]],a[[i]]])],
		{i,Length[pos]}
	];
	ReplacePart[e,rule];
	e=e/(u Log[a[[1]]]);
	Print[u];
	Return[Integrate[e,y]//.u->a[[1]]^x]*)
];
