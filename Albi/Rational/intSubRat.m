(* ::Package:: *)

(* this function is part of utilities of Albi*)
(* See page 75 of Symbolic integration by Bronstein*)
(* This part change the output of RothsteinTrager from Log form to ArcTan form:
	I Log[(A + B I)/(A - B I)] --> 2ArcTan(A/B)   *)
(* This part need package .\\Rational \\ Rioboo.m*)
Log2ArcTan[f_,x_]:=Module[
	{e},
	e = f//.ci1_ Log[vi1_]+ci2_ Log[vi2_]/;FreeQ[Simplify[ci1+ci2],Complex]
		->(Simplify[ci1+ci2])/2 Log[Simplify[((vi1+vi2)/2)^2+((vi1-vi2)/2/I)^2]] + Simplify[ci1-ci2]/2/I Calculus`Albi`Rational`LogToAtan[((vi1+vi2)/2),((vi1-vi2)/2/I),x];
	e = FullSimplify[e];
	Return[e];
]

