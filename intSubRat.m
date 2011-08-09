(* ::Package:: *)

intSubRat[f_,x_]:=Catch[Module[
	{},
	Print["It's a rational function.Need to Integrate[",f,",",x,"]"];
	Throw[Integrate[f,x]]
]]	
