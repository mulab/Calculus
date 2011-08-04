(* ::Package:: *)

(* Method 6 in Stage II, (6)trigonometirc functions *)
(* Last revised by ivan on July 28, 2011. Email: ma_wan _li .6209@163.com *)
intSubTri[f_, x_]:=Module[
	{e},
	e=Trans1[f,x];
	If[Length[e]==2,Return[e]];
	e=Trans2[f,x,x];
	e=Trans3[e[[1]],e[[2]],e[[3]]];
	e=Trans4[e[[1]],e[[2]],e[[3]]];
	e=Trans5[e[[1]],e[[2]],e[[3]]];
	e=Trans6[e[[1]],e[[2]],e[[3]]];

	Return[e];
]
(* Attention! function Simplify should be used carefully. 
	Sometimes it causes problems; I mean it make some expression more complicated*)


(*exp1=(Sin[x])^2;
intSubTri[exp1,x]
exp2=Sqrt[A^2+B^2(Sin[x])^2]/Sin[x];
intSubTri[exp2,x]
exp3=1/(1+Cos[x]);
intSubTri[exp3,x]


intSubTri[Cos[3 x] Cos[n x],x]
intSubTri[Tan[Sin[x+5]]/Exp[5+x],x]
intSubTri[(Sin[z])^2(Cos[z])^3,z]

exp1=(Sin[x])^(-5)*Exp[(Sin[x])^10+Cos[x]+(Sin[x])^(-2)];
intSubTri[exp1,x]
exp2=(Cos[x])^(3)*Exp[(Sin[x])+(Cos[x])^(-2)];
intSubTri[exp2,x]	

exp1=Tan[x]+Exp[(Cos[x])^10+1/(Cos[x])^2];
intSubTri[exp1,x]
exp2=Cot[x]+Exp[(Sin[x])^10+1/(Tan[x])^2];
intSubTri[exp2,x]

intSubTri[1/(1+Cos[x]),x]*)


(* part I) In problems where the arguments of the trigonometric functions are not the same throughout the integrand, the following cases are examined*)

Trans1[f_, x_]:=Module[
	{e=f,m,mm,n,part1,part2,triin1,triin2},
	If[Head[e] === Times,
		part1=Level[e,1][[1]];
		part2=Level[e,1][[2]];
		If[Head[part1]===Cos && Head[part2]===Sin,(* Int:Sin[mx]Cos[nx] *)
			triin1=Level[part1,1][[1]];(* inner of Cos*)
			triin2=Level[part2,1][[1]];(* inner of Sin*)
			If[triin1 === x,(*find the coef of x in Cos*)
				n=1,
				If[MatchQ[triin1, a_ x],n = triin1/x,Return["NotMatch"]];
			];
			If[triin2 === x,(*find the coef of x in Sin*)
				m=1,
				If[MatchQ[triin2, a_ x],m = triin2/x,Return["NotMatch"]];
			];
			If[!FreeQ[m,x],Return["NotMatch"]];(*m and n cannot contain variable x*)
			If[!FreeQ[n,x],Return["NotMatch"]];
			If[m===n,Return[{-Cos[(m+n) x]/2/(m+n),x}]];
			If[m===-n,Return[{-Cos[(m-n) x]/2/(m-n),x}]];
			Return[{-Cos[m x-n x]/2/(m-n)-Cos[m x+n x]/2/(m+n),x}];
		];

		If[Head[part1]===Sin && Head[part2]===Sin,(* Int:Sin[mx]Sin[nx] *)
			triin1=Level[part1,1][[1]];(* inner of Cos*)
			triin2=Level[part2,1][[1]];(* inner of Sin*)
			If[triin1 === x,(*find the coef of x in Cos*)
				n=1,
				If[MatchQ[triin1, a_ x],n = triin1/x,Return["NotMatch"]];
			];
			If[triin2 === x,(*find the coef of x in Sin*)
				m=1,
				If[MatchQ[triin2, a_ x],m = triin2/x,Return["NotMatch"]];
			];
			If[!FreeQ[m,x],Return["NotMatch"]];(*m and n cannot contain variable x*)
			If[!FreeQ[n,x],Return["NotMatch"]];
			Return[{Sin[m x-n x]/2/(m-n)-Sin[m x+n x]/2/(m+n),x}];
		];

			If[Head[part1]===Cos && Head[part2]===Cos,(* Int:Cos[mx]Cos[nx] *)
			triin1=Level[part1,1][[1]];(* inner of Cos*)
			triin2=Level[part2,1][[1]];(* inner of Sin*)
			If[triin1 === x,(*find the coef of x in Cos*)
				n=1,
				If[MatchQ[triin1, a_ x],n = triin1/x,Return["NotMatch"]];
			];
			If[triin2 === x,(*find the coef of x in Sin*)
				m=1,
				If[MatchQ[triin2, a_ x],m = triin2/x,Return["NotMatch"]];
			];
			If[!FreeQ[m,x],Return["NotMatch"]];(*m and n cannot contain variable x*)
			If[!FreeQ[n,x],Return["NotMatch"]];
			Return[{Sin[m x-n x]/2/(m-n)+Sin[m x+n x]/2/(m+n),x}];
		];
	(*else*)Return[{e,x,x}]
	](*endif*)
]

(* Attention: input expr cannot contain coef, even -1. So input Cos[n x] Sin[-m x] will cause error because coef=-1 will be added on expr *)


(*ans=Trans1[Cos[3 x] Cos[n x],x]*)


(* part II) If the arugments are the same but are not identically x, 
	a linear substitution y = a+bx is performed
	??? and the procedure continues with the revised problem.
	OTHERWISE,Return the third*)

Trans2[f_, x_, xt_]:=Module[
	{e=f,pos,a,b,yx,linearexp,y},
	pos=Position[f,a_ x + b_];
	If[Length[pos]>0,
		(*a=Level[Extract[f,pos[[1]]],1][[1]];*)
		b=Extract[f,pos][[1,1]];
		a=Extract[f,pos][[1,2,1]];
		If[!FreeQ[a,x],Return[{f, x, xt}]];
		If[!FreeQ[b,x],Return[{f, x, xt}]];
		e = e/.(-a x - b)->-y;
		e = e/.(a x + b)->y; (* replace ax+b by y, if x still exists, fail *)
		yx = a x + b;
		If[FreeQ[e,x],Return[{e,y,yx/.x->xt}],Return[{f, x, xt}]]; 
	];

	pos=Position[f,a_ x];
	If[Length[pos]>0,
		(*a=Level[Extract[f,pos[[1]]],1][[1]];*)
		a=Extract[f,pos][[1,1]];
		b=0;
		If[!FreeQ[a,x],Return[{f, x, xt}]];
		e = e/.(-a x)->-y;
		e = e/.(a x)->y; (* replace ax+b by y, if x still exists, fail *)
		yx = a x ;
		If[FreeQ[e,x],Return[{e,y,yx/.x->xt}],Return[{f, x, xt}]]; 
	];

	pos=Position[e,b_ + x];
	If[Length[pos]>0,
		(*a=Level[Extract[f,pos[[1]]],1][[1]];*)
		a=1;
		b=Extract[f,pos][[1,1]];

		If[!FreeQ[b,x],Return[{f, x, xt}]];
		e = e/.(b+x)->y;
		e = e/.(-b-x)->-y; (* replace ax+b by y, if x still exists, fail *)
		yx = b+x ;
		If[FreeQ[e,x],Return[{e,y,yx/.x->xt}],Return[{f, x, xt}]]; 
	];

	Return[{f, x, xt}];
]


(*Trans2[Tan[Sin[x+5]]/Exp[5+x],x,t^2]*)


(* part III *)
(* All Sin[y] are replaced by sin[x] in order to prevent being simplified by system*)
Trans3[f_, x_, xt_]:=Module[
	{e,sin,cos,coef,part1,part2,m=0,n=0,y},

	e = Simplify[f];
	If[Head[e]===Times && FreeQ[Level[e,1][[1]],x],(*coef exists*)
		coef = Level[e,1][[1]];
		e = e/coef,
		coef=1;
	];

	e = e /.Sin[x]->sin /.Cos[x]->cos;
	e = e /.Tan[x]->sin/cos /. Cot[x]->cos/sin;
	e = e /.Csc[x]->1/sin /.Sec[x]->1/cos;

	If[MatchQ[e,(cos)^nn_ (sin)^mm_],n=Level[e,2][[2]];m=Level[e,2][[5]]];
	If[MatchQ[e,(cos)^nn_ sin],n=Level[e,2][[2]];m=1];
	If[MatchQ[e,cos (sin)^mm_],n=1;m=Level[e,2][[3]]];
	If[MatchQ[e,(cos)^nn_],n=Level[e,2][[2]];m=0];
	If[MatchQ[e,(sin)^mm_],n=0;m=Level[e,2][[2]]];

	If[m==0&&n==0,Return[{f, x, xt}];];

	If[m<n,Return[{coef*(Sin[2 y]/2)^m (1/2+Cos[2 y]/2)^(n/2-m/2),y,x/.x->xt}],
		Return[{coef*(Sin[2 y]/2)^n (1/2-Cos[2 y]/2)^(m/2-n/2),y,x/.x->xt}]];
]
	
(*Problems remains:
	do not support situations when m or n is negative, ex. sin(x)tan(x)*)


(*HISTORY VERSION
(* part III *)
(* !!This part should be revised to satisfy strictly designed test!!*)

Trans3[f_, x_, xt_]:=Module[
	{e=Simplify[f],coef,part1,part2,m,n,y},
	If[Head[e]===Times,
		part1=Level[e,1][[1]];
		If[FreeQ[part1,x],
			coef=part1;
			e=f/coef;
			part1=Level[e,1][[1]],
			coef=1;
		];
		part2=Level[e,1][[2]],
	(*else if*)(*m or n might be zero*)
		If[Head[e]===Cos,part1=e;part2=1,If[Head[e]===Sin,part2=e;part1=1,Return[{f, x, xt}];]];
	];
	If[Head[part1]===Power,
		n=Level[part1,1][[2]];
		If[!IntegerQ[n],Return[{f, x, xt}]];
		cospart=Level[part1,1][[1]];
		If[cospart=!=Cos[x],Return[{f, x, xt}]],
	(*else if*)(* Special situation when n=0 or 1*)
		If[part1===1,n=0,If[part1===Cos[x],n=1,Return[{f, x, xt}];];];
	];
	If[Head[part2]===Power,
		m=Level[part2,1][[2]];
		If[!IntegerQ[m],Return[{f, x, xt}]];
		sinpart=Level[part2,1][[1]];
		If[sinpart=!=Sin[x],Return[{f, x, xt}]],
	(*else if*)(* Special situation when m=0 or 1*)
		If[part2==1,m=0,If[part2===Sin[x],m=1,Return[{f, x, xt}];];];
	];
	If[m<n,Return[{coef*(Sin[2 y]/2)^m (1/2+Cos[2 y]/2)^(n/2-m/2),y,x/.x->xt}],
		Return[{coef*(Sin[2 y]/2)^n (1/2-Cos[2 y]/2)^(m/2-n/2),y,x/.x->xt}]];
]
(*Problems remains:
	do not support situations when m or n is negative, ex. sin(x)tan(x)*)
*)


(*Trans3[(Sin[z])^(4)(Cos[z])^7,z,t]*)


(* part IV: All trigonometric functions are transformed into sines and cosines *)
(* All Sin[y] are replaced by sin[y] in order to prevent being simplified by system*)
(* I first try to replace this variables and then test whether throughly*)
Trans4[f_, y_, yx_]:=Module[
	{e,d,m,n,z,sin,cos},(* transform to sin and cos*)
	e = Simplify[f] /.Sin[y]->sin[y] /.Cos[y]->cos[y];
	e = e /.Tan[y]->sin[y] /cos[y]/.Cot[y]->cos[y]/sin[y];
	e = e /.Csc[y]->1/sin[y] /.Sec[y]->1/cos[y];

	d=e;(*e: to test whether mathch situation a); d: whether b)*)

	e = e /(-sin[y]);(*if z=cos(y), dz=-sin(y)dy, so at first devide -sin(y)*)
	e=e/. cos[y]->z;(*replace cos(y)*)
	e=e/.n_Integer->2**(n/2);(*see "**". In order to test whether n is even*)
	e=e/.(sin[y])^(2**m_Integer)->(1-z^2)^m;
			(* If n is even, here m should be integer, so replaced by 1-z^2*)	
	e=e/. 2**n_->2 n;(*recover e*)	
	If[FreeQ[e,y],Return[{e,z,Cos[y]/.y->yx}]];

	d = d /(cos[y]);(*if z=sin(y), dz=c0s(y)dy, so at first devide cos(y)*)
	d=d/. sin[y]->z;(*recover e*)
	d=d/.n_Integer->2**(n/2);(*see "**". In order to test whether n is even*)
	d=d/.(cos[y])^(2**m_Integer)->(1-z^2)^m;
			(* If n is even, here m should be integer, so replaced by 1-z^2*)	
	d=d/. 2**n_->2 n;(*recover e*)	
	If[FreeQ[d,y],Return[{d,z,Sin[y]/.y->yx}],Return[{f, y, yx}]];
]


(*exp1=(Sin[x])^(-5)*Exp[(Sin[x])^10+Cos[x]+(Sin[x])^(-2)]
Trans4[exp1,x,x]
exp2=(Cos[x])^(3)*Exp[(Sin[x])+(Cos[x])^(-2)]
Trans4[exp2,x,x]	
exp3=Sqrt[A^2+B^2(Sin[x])^2]/Sin[x]
Trans4[exp3,x,x]	*)


(* part V: All trigonometric functions are transformed into secants and tangents *)
(* Just like part IV, are trigonometirc functions are rewritten in lowercase 
	in order to prevent simplification*)
Trans5[f_, y_, yx_]:=Module[
	{e,d,m,n,z,tan,sec},(* transform to tan and sec*)
	e = f /. Sin[y] -> tan[y]/sec[y] /. Cos[y] -> 1/sec[y];
	e = e /. Tan[y] -> tan[y] /. Cot[y] -> 1/tan[y];
	e = e /. Csc[y] -> sec[y]/tan[y] /. Sec[y] -> sec[y];

	e = e /((sec[y])^2);(*if z=tan(y), dz=sec^2(y)dy, so at first devide sec^2*)
	e = e /. tan[y] -> z;(*replace tan(y)*)
	e = e /. n_Integer -> 2 ** (n/2);(*see "**". In order to test whether n is even*)
	e = e /. (sec[y])^(2 ** m_Integer) -> (1 + z^2)^m;(* sec^2=1+tan^2=1+z^2*)
			(* If n is even, here m should be integer, so replaced by 1-z^2*)	
	e = e /. 2 ** n_ -> 2 n;(*recover e*)	
	If[FreeQ[e, y], Return[{e, z, Tan[y]/.y->yx}],Return[{f, y, yx}]]
(*
(*Here also detect the integrand with form: Elem(cot(y),csc^2(y))
but, this part seems to work the same as Elem(tan(y),sec^2(y),NEGLECT! *)
	d = f /.Sin[y]->1/csc[y] /.Cos[y]->cot[y]/csc[y];
	d = d /.Tan[y]->1/cot[y]/.Cot[y]->cot[y];
	d = d /.Csc[y]->csc[y] /.Sec[y]->csc[y]/cot[y];

	d = d /(-(csc[y])^2);(*if z=cot(y), dz=-csc^2(y)dy, so at first devide -csc^2*)
	d=d/. cot[y]->z;(*replace cot(y)*)
	d=d/.n_Integer->2**(n/2);(*see "**". In order to test whether n is even*)
	d=d/.(csc[y])^(2**m_Integer)->(1+z^2)^m;(* csc^2=1+cot^2=1+z^2*)	
	d=d/. 2**n_->2 n;(*recover d*)	
	If[FreeQ[d,y],Return[{d,z,Cot[y]/.y->yx}],Return[{f, y, yx}]];*)
]
(*This paragraph of code should be examined. I suspect there remains some error*)


(*exp1=Tan[x]+Exp[(Cos[x])^10+1/(Cos[x])^2]
Trans5[exp1,x,x]
exp2=Cot[x]+Exp[(Sin[x])^10+1/(Tan[x])^2]
Trans5[exp2,x,x]
Trans5[1/2-1/2*Cos[2*x],x,x]*)


(* part VI: Finally, the substitution z=tan(y/2)=sin (y)/(z+cos(y)) is made *)
(* Just like part IV and V, see comments there*)
Trans6[f_, y_, yx_]:=Module[
	{e,z},(* transform to sin and cos*)
	e = Simplify[f](* /. Sin[y] -> sin[y] /. Cos[y] -> cos[y];
	e = e /. Tan[y] -> tan[y] /. Cot[y] -> cot[y];
	e = e /. Csc[y] -> csc[y] /. Sec[y] -> sec[y]*);
(*z=sin/(1+cos)=(1-cos)/sin*)
	e = e*(1+Cos[y]);
(*if z=tan(y/2), dz=dy/(1+cos(y)), so at first times (1+cos(y)) *)
	
	e = e/.(1+Cos[y])->Sin[y]/z;
	e = e/.(1-Cos[y])->Sin[y]*z;
	e = Simplify[e];

	If[FreeQ[e, y], Return[{e, z, (Sin[y]/(1+Cos[y])/.y->yx)}],Return[{f, y, yx}]]
]


(*Trans6[1/(1+Cos[x]),x,x]*)


(*------------------------------------------------------------------------*)
(*------------------------------------------------------------------------*)
(*------------------------------------------------------------------------*)
(*belowing this is not written by me. __ivan*)
(*------------------------------------------------------------------------*)
(*------------------------------------------------------------------------*)
(*------------------------------------------------------------------------*)
(*If f has the form a*x+b,a and b are constants,this function returns the coefficients,otherwise returns Null*)
(*Lineart[f_,x_,a_,b_]:=Module[
	{m=a,n=b,temp},
	Switch[f,
 	_Plus,(*the form is m*x+n*)
 	If[! FreeQ[temp = Level[f, 1][[1]], x],(*temp=m*x*)
  		If[m =!= Null,
   			If[m != temp/x || n != f - temp,
    				Return[]
    			],
   			m = temp/x;
   			If[! FreeQ[m, x],
    				Return[]
    			];
   			n = f - temp;
   			If[! FreeQ[n, x],
    				Return[]
    			]
   		],
  		(*temp=n*)
  		If[m =!= Null,
   			If[n != temp || m != (f - temp)/x,
    				Return[]
    			],
   			n = temp;
   			m = (f - temp)/x;
   			If[! FreeQ[m, x],
    				Return[]
    			]
   		]
  	];
 	Return[{m, n}],
 	_,(*the form is m*x or x*)
 	If[n =!= Null,
  		If[n != 0 || m != f/x,
   			Return[]
   		],
  		n = 0
  	];
 	m = f/x;
 	If[! FreeQ[m, x],
  		Return[]
  	];
 	Return[{m, n}]
 	]	
]*)


(*Lineart[Sin[3x+5],x,3,5]
Print["this"]*)


(*The integrand is an elementary function of the trigonometric function applied to linear argument in the variable of integration.*)
(*intSubTri2[f_,x_]:=Catch[
	Module[
	{e=f,pos,loci,triArg,triFun={{},{},{},{},{},{}},a=Null,b=Null,n,temp,s,trigList,i},
	tri={Sin,Cos,Tan,Cot,Sec,Csc};
	Do[
		pos=Position[e,tri[[k]][_]];(*gives the position of Trig (ax+b)*)
		(*Is the pattern of Trig (ax+b)*)
		Do[
			loci=pos[[i]];
			triArg=Extract[e,Append[loci,1]];(*triArg=a*x+b*)
			If[!FreeQ[triArg,x],
				If[linear[triArg,x,a,b]=!=Null,
					{a,b}=linear[triArg,x,a,b];
					AppendTo[triFun[[k]],loci],
					Throw["NotMatch"]
				]
			],
			{i,Length[pos]}
		];
		e=ReplacePart[e,triFun[[k]]->tri[[k]][t]],(*substitute Trig (ax+b) to Trig (t)*)
		{k,Length[tri]}
	];
	If[triFun[[1]]=={}&&triFun[[2]]=={},
		Throw["NotMatch"]
	];                                                           (*\:6743\:5b9c\:4e4b\:7b56\:ff0c\:6b64\:65b9\:6cd5\:4ee5\:540e\:5c1a\:9700\:5927\:7684\:6539\:8fdb*)
	(*Now has got all the trig information of f*)
	(*transform all trigonometric functions into sines and cosines,not done...*)

	(*transform the form Sin[x]^m*Cos[x]^n:NEEDED?*)
	
	(*cases that can substitute z=cosy or z=siny*)
	If[Head[e]===Times,
		temp=Part[e,1];
		trigList={Sin,Cos};
		For[i=1,i<3,i++,
		If[MatchQ[temp,trigList[[i]][t]^_Integer] && OddQ[Part[temp,2]],
			n=(Part[temp,2]-1)/2;
			temp=e/temp,
			If[MatchQ[e/temp,trigList[[i]][t]^Integer] && OddQ[Part[e/temp,2]],
				n=(Part[e/temp,2]-1)/2,
				If[MatchQ[temp,trigList[[i]][t]],
					n=0;
					temp=e/temp,
					If[MatchQ[e/temp,trigList[[i]][t]],
						n=0,
						Continue[]
					]
				]
			]
		];(*now temp is Elem (sint^2,cost) or Elem (cost^2,sint)*)
		pos=Position[temp,trigList[[i]][t]];
		Do[
			loci=pos[[i]];
			If[Head[s=Extract[temp,Delete[loci,-1]]]===Power&&Part[s,2]===2,
				temp=ReplacePart[temp,Delete[loci,-1]->1-y^2]
			],
			{i,Length[pos]}
		];
		If[i==1,
			temp=ReplacePart[temp,Position[temp,Cos[t]]->y];
			Throw[{-(1-y^2)^n*temp/a,y}],
			temp=ReplacePart[temp,Position[temp,Sin[t]]->y];
			Throw[{(1-y^2)^n*temp/a,y}]
		]
		](*For cycle end*)
	];

	(*Cases that can substitute z=tany*)
	If[triFun[[1]]=={}&&triFun[[2]]=={}&&triFun[[4]]=={}&&triFun[[6]]=={},(*to transform to Elem (tant,sec^2 t   and temp=f*)
		temp=e;
		pos=Position[temp,Sec[t]];
		Do[
			loci=pos[[i]];
			If[Head[s=Extract[temp,Delete[loci,-1]]]===Power&&Part[s,2]===2,
				temp=ReplacePart[temp,Delete[loci,-1]->1+y^2]
			],
			{i,Length[pos]}
		];
		temp=ReplacePart[temp,Position[temp,Tan[t]]->y];
		Throw[{1/(1+y^2)*temp/a,y}];
	];
	(*substitute z=tan1/2*y*)		
	If[triFun[[1]]=!={},e=ReplacePart[e,triFun[[1]]->2y/(1+y^2)]];
	If[triFun[[2]]=!={},e=ReplacePart[e,triFun[[2]]->(1-y^2)/(1+y^2)]];
	If[triFun[[3]]=!={},e=ReplacePart[e,triFun[[3]]->2y/(1-y^2)]];
	If[triFun[[4]]=!={},e=ReplacePart[e,triFun[[4]]->(1-y^2)/(2y)]];
	If[triFun[[5]]=!={},e=ReplacePart[e,triFun[[5]]->(1+y^2)/(1-y^2)]];
	If[triFun[[6]]=!={},e=ReplacePart[e,triFun[[6]]->(1+y^2)/(2y)]];
	Throw[{Simplify[2/(1+y^2)*e/a],y}];

	Throw["NotMatch"](*!!Need improve,return transformed expressions,so are the aboves*)
]
]
	
*)


(*intSubTri2[(6 (1/y^6)^(1/6) (y^6)^(2/3))/(-1+(y^6)^(1/6)),y]
intSubTri2[Sin[2 x],x]*)









