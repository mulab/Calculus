(* ::Package:: *)

(* Method 8 in Stage II, (4)Chebyshev *)
(* Last revised by ivan on 18:49 Aug 1, 2011. Email: ma_wan _li .6209@163.com *)
(* I ONLY changed the following part of the original code:
  a)interface of this function: revise return to {expr,y,yx} in which y is the variable of expr and yx is the relationship between y and x
*)

(*aaThe integrand is not a rational function and possesses the form ax^r*(c1+c2*x^q)*p,
where A,c1,c2 are constants,p,q,r are rational numbers and c1*c2*q*p!=0*)
intSubBin[f_,x_]:=Module[
	{e=f,l,part,i,se,se1,se2,a=1,r,p,q,c1,c2,r1,r2,d},
	If[Head[e]===Times,
		l=Length[e];
		part=Table[Part[e,i],{i,l}];
		For[i=1,i<=l,i++,
			If[FreeQ[part[[i]],x],
				a=a*part[[i]]
			]
		];
		se=e/a;(*se=x^r*(c1+c2*x^q)^p*)
		se1=Part[se,1];(*se1=x^r*)
		se2=se/se1;(*se2=(c1+c2*x^q)^p*)
		If[Head[se1]===Power&&(Head[Part[se1,2]]===Integer||Head[Part[se1,2]]===Rational),
			r=Part[se1,2],
			If[se1===x,(*r=1\:7684\:60c5\:5f62*)
				r=1,
				Return["NotMatch"]
			]
		];
		If[Head[se2]===Power&&(Head[Part[se2,2]]===Integer||Head[Part[se2,2]]===Rational),
			p=Part[se2,2];
			se=Part[se2,1];(*se=c1+c2*x^q,condition:c1,c2,q!=0*)
			If[Head[se]===Plus,
				If[FreeQ[c1=Part[se,1],x],
					se=se-c1,
					se=c1;
					c1=se-c1
				];(*se=c2*x^q*)
				If[!FreeQ[c1,x],
					Return["NotMatch"]
				];
				If[Head[se]===Times&&MatchQ[Part[se,2],x^q_],(*c2!=1*)
					c2=Part[se,1];
					If[!FreeQ[c2,x],
						Return["NotMatch"]
					];
					If[Head[q=Part[Part[se,2],2]]=!=Integer&&Head[q]=!=Rational,
						Return["NotMatch"]
					],
					If[MatchQ[se,x^q_],(*c2=1*)
						c2=1;
						If[Head[q=Part[se,2]]=!=Integer&&Head[q]=!=Rational,
							Return["NotMatch"]
						],
						If[se==x,
							c2=1;
							q=1,
							Return["NotMatch"]
						]
					]
				],
				Return["NotMatch"]
			],
			Return["NotMatch"]
		];
		r2=p;
		r1=(r+1)/q-1;
		If[Head[r1]===Integer&&r2>0,(*substitute y=c1+c2*x^q*)
			e=e/(c2*q*x^(q-1));
			e=e/.x->((y-c1)/c2)^(1/q);
			Return[{Simplify[e],y,c1+c2*x^q}]
		];
		If[Head[r2]===Integer&&Head[r1]===Rational,(*substitute y=x^(q/d1),d1 is the denominator of r1*)
			d=Denominator[r1];
			e=e/(q/d*x^(q/d-1));
			e=e/.x->y^(d/q);
			Return[{Simplify[e],y,x^(q/Denominator[r1])}]
		];
		If[Head[r1]===Integer&&r1<0&&Head[r2]===Rational,(*substitute y=(c1+c2*x^q)^(1/d2),d2 is the denominator of r2*)
			d=Denominator[r2];
			e=e/((c2*q/d)*x^(q-1)*(c1+c2*x^q)^(1/d-1));
			e=e/.x->((y^d-c1)/c2)^(1/q);
			Return[{Simplify[e],y,(c1+c2*x^q)^(1/Denominator(r2))}]
		];
		If[Head[r1+r2]===Integer,(*substitute y=((c1+c2*y)/y)^(1/d1),d1 is the denominator of r1*)
			d=Denominator[r1];
			e=e/((-q*c1/d)*(c1/x^q+c2)^(1/d-1)/x^(q+1));
			e=e/.x->(c1/(y^d-c2))^(1/q);
			Return[{Simplify[e],y,((c1+c2*x^q)/x^q)^(1/Denominator[r1])}]
		],
		Return["NotMatch"]
	]
]
assertion


(*Test:*)
intSubBin[x^4*(1-x^2)^(-5/2),x]
intSubBin[x^(1/2)*(1+x)^(5/2),x]







