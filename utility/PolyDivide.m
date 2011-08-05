(* ::Package:: *)

PolyDivide[a_,b_,x_]:=Module[
	{Q=0,R=Simplify[a],B=Simplify[b],\[Delta],T,nR,nB},
	nR=Exponent[R,x];
	nB=Exponent[B,x];
	While[R=!=0&&(\[Delta]=nR-nB)>=0,
		T=(Coefficient[R,x,nR]/Coefficient[B,x,nB])*x^\[Delta];
		Q=Q+T;
		R=Simplify[R-B*T];
		nR=Exponent[R,x];
	];
	{Q,R}
]


PolyPseudoDivide[A_,B_,x_]:=Module[
	{Q=0,R=Simplify[A],T,b,nR,nB,N,\[Delta]},
	nR=Exponent[R,x];
	nB=Exponent[B,x];
	b=Coefficient[B,x,nB];
	N=Exponent[A,x]-Exponent[B,x]+1;
	While[R=!=0&&(\[Delta]=nR-nB)>=0,
		T=Coefficient[R,x,nR]*x^\[Delta];
		N--;
		Q=b*Q+T;
		R=Simplify[b*R-T*B];
		nR=Exponent[R,x];
	];
	{b^N*Q,b^N*R}
]


(* PolyDivide[3x^3+x^2+x+5,5x^2-3x+1,x]
PolyPseudoDivide[3x^3+x^2+x+5,5x^2-3x+1,x] *)
