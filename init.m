(* ::Package:: *)

BeginPackage["Calculus`"];
D::usage="";
CWD::usage="Current Work Directory";
IntegrateU::usage="IntegrateU[f[x],x] returns the integral";


Begin["`Private`"];
(*\:7531\:4e8eNotebookDirectory[]\:63d0\:53d6\:7684\:662f\:6700\:521d\:6267\:884c\:7684\:6587\:4ef6\:6240\:5728\:5b50\:76ee\:5f55\:ff0c\:6545\:624b\:5de5\:8bbe\:7f6eCWD\:6765\:786e\:5b9a\:5b50\:76ee\:5f55*)
CWD=NotebookDirectory[];
Get[CWD<>"\\utility\\init.m"];
Get[CWD<>"\\Rubi\\init.m"];
Get[CWD<>"\\Albi\\init.m"];
(* Get[NotebookDirectory[]<>"D.u"]; *)
Get[CWD<>"Integrate.m"];
End[];


EndPackage[];
