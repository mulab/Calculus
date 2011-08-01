(* ::Package:: *)

(*This method is used whenever all of the previous methods have failed to be applicable.
No clue for the applicability of this method is found by FORM.*)
(*What about FORM? A speical pattern for dealing with expression*)
(*the last method of SIN StageII, Moses*)
(*Shao Qiming*)
intSubEps[f_,x_]:=Module[
{e=f},
e=Expand[e];(*\:5e42\:7ea7\:6570\:5c55\:5f00\:548c\:4e58\:6cd5\:5c55\:5f00,Using Expand*)
Return[{e,x}]
]


intSubEps[x(Cos[x]+Sin[x]),x]
intSubEps[(x+E^x)/x,x]
intSubEps[x (1+E^x)^2,x]



