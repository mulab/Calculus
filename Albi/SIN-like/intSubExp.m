(* ::Package:: *)

(*gives the indefinite integral of elementary function of exponentials by transforming 
Subscript[a, i]^(Subscript[b, i]x+Subscript[c, i]) into 
Subscript[a, i]^Subscript[c, i]*Subscript[a, 1]^(Subscript[b, i]x*Log[Subscript[a, 1],Subscript[a, i]]),
 and then mading the substitution y=Subscript[a, 1]^x*)
(*the method 1 of SIN ( Symbolic INtegrator ) stage II*)
(*Shao Qiming & Zhang Junlin*)
intSubExp[f_,x_]:=Module[
	{e=f,pos=Position[f,x],loc={},i,j,len,ptr,mp,a={},b={},c={},y,ans},
	If[Length[pos]==0,Return["NotMatch"]];
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
			(*is 1*)(*else*)
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
		(*Extract\:4e0d\:652f\:6301Extract[expr,{}]*)
		If[Head[Extract[e,{ptr}][[1]]]=!=Power||j!=2(*b*x+c is not the second part*),
			Return["NotMatch"]
		];
		(*If[b[[-1]]==0&&c[[-1]]==1,b=Delete[b,-1];c=Delete[c,-1];Print["xxx"];Continue[]];*)
		AppendTo[a,Extract[e,Append[ptr,1]]];
		If[!FreeQ[a[[i]],x],
			Return["NotMatch"]
		];
		AppendTo[loc,ptr],
		{i,Length[pos]}
	];
	(*Print[{a,b,c}];*)
	If[ans!=Null,
		Return[ans]
	];
	(*Although I do not know what's meaning of below sentence, it is geilivable*)
	If[Length[a]!=Length[b]||Length[a]!=Length[c]||Length[b]!=Length[c],Return["NotMatch"]];
	Do[(*construct the rule list*)
		loc[[i]]=Rule[loc[[i]],a[[i]]^c[[i]]*y^(b[[i]]*Log[a[[1]],a[[i]]])],
		{i,Length[pos]}
	];
	If[Length[loc]==1&&loc[[1,1]]=={},(*ReplacePart can't deal with the rule like {{}->y}*)
		e=a[[1]]^c[[1]]*y^b[[1]],
		e=ReplacePart[e,loc]
	];
	e=e/(y*Log[a[[1]]]);

	Return[{e,y,a[[1]]^x}]


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
]


(*intSubExp[E^x/(2+3E^(2x)),x]
intSubExp[E^(2x)/(a+b E^(4x)),x]
intSubExp[E^(x+1)/(1+E^x),x]
intSubExp[10^x E^x,x]
intSubExp[(a+b^(c x+h))/(d+e^(f x+g)),x]
intSubExp[a^x/b^x,x]*)
(*intSubExp[x/(1+E^x),x]
intSubExp[x/(1+x),x]
intSubExp[1/1+x,x]*)
(*intSubExp[x,x]*)
(*\:8be5\:51fd\:6570\:53ea\:8981\:5b58\:5728a^(b x+c)\:ff0c\:5c31\:4f1a\:5904\:7406\:ff0c\:9664\:6b64\:4e4b\:5916\:ff0c\:4e0d\:4f1a\:5bf9\:5176\:5b83\:7c7b\:578b\:7684x\:6240\:7ed9\:7684\:4fe1\:606f\:7ed9\:51fa\:591a\:4f59\:7684\:5224\:65ad...*)
(*intSubExp[E^x/(E^(x)+1),x]
intSubExp[E/x,x]*)
