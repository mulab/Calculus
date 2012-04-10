(* ::Package:: *)

Print["test utility function"]
Test[file_String] := Module[{lst},
Print["test string"];
Do[Test[lst],{lst,ReadList[file]}]
]
Test[lst_List] := Module[{result},
(*result = Calculus`Rubi`Int[lst[[1]],lst[[2]]];*)
result = Integrate[lst[[1]],lst[[2]]]
If[!FreeQ[result, Calculus`Rubi`Int], result = $Failed];
Print["tested"];
If[!(result == lst[[4]]),Print[lst[[1]]," : ",result];Print[":-( ",lst[[4]]]];(*Input[]*)]
