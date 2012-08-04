(* ::Package:: *)

(* ::Code:: *)
Int[ArcCoth[a_.*x_],x_Symbol] :=
(Print["Int(1th)@InverseHyperbolicCotangentFunctions.m"];
  x*ArcCoth[a*x] + Log[1-a^2*x^2]/(2*a)) /;
FreeQ[a,x]

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_,x_Symbol] :=
(Print["Int(2th)@InverseHyperbolicCotangentFunctions.m"];
  x*ArcCoth[a*x]^n -
  Dist[a*n,Int[x*ArcCoth[a*x]^(n-1)/(1-a^2*x^2),x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>1

(* ::Code:: *)
Int[x_*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(3th)@InverseHyperbolicCotangentFunctions.m"];
  -ArcCoth[a*x]^n/(2*a^2) + x^2*ArcCoth[a*x]^n/2 +
  Dist[n/(2*a),Int[ArcCoth[a*x]^(n-1),x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(4th)@InverseHyperbolicCotangentFunctions.m"];
  -x^(m-1)*ArcCoth[a*x]^n/(a^2*(m+1)) + x^(m+1)*ArcCoth[a*x]^n/(m+1) +
  Dist[n/(a*(m+1)),Int[x^(m-1)*ArcCoth[a*x]^(n-1),x]] +
  Dist[(m-1)/(a^2*(m+1)),Int[x^(m-2)*ArcCoth[a*x]^n,x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0 && RationalQ[m] && m>1

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_/x_,x_Symbol] :=
(Print["Int(5th)@InverseHyperbolicCotangentFunctions.m"];
  2*ArcCoth[a*x]^n*ArcCoth[1-2/(1-a*x)] -
  Dist[2*a*n,Int[ArcCoth[a*x]^(n-1)*ArcCoth[1-2/(1-a*x)]/(1-a^2*x^2),x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>1

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_./x_^2,x_Symbol] :=
(Print["Int(6th)@InverseHyperbolicCotangentFunctions.m"];
  -ArcCoth[a*x]^n/x +
  Dist[a*n,Int[ArcCoth[a*x]^(n-1)/(x*(1-a^2*x^2)),x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_./x_^3,x_Symbol] :=
(Print["Int(7th)@InverseHyperbolicCotangentFunctions.m"];
  a^2*ArcCoth[a*x]^n/2 - ArcCoth[a*x]^n/(2*x^2) +
  Dist[a*n/2,Int[ArcCoth[a*x]^(n-1)/x^2,x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(8th)@InverseHyperbolicCotangentFunctions.m"];
  x^(m+1)*ArcCoth[a*x]^n/(m+1) - a^2*x^(m+3)*ArcCoth[a*x]^n/(m+1) -
  Dist[a*n/(m+1),Int[x^(m+1)*ArcCoth[a*x]^(n-1),x]] +
  Dist[a^2*(m+3)/(m+1),Int[x^(m+2)*ArcCoth[a*x]^n,x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0 && RationalQ[m] && m<-3

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
(Print["Int(9th)@InverseHyperbolicCotangentFunctions.m"];
  -ArcCoth[a*x]^n*Log[2*c/(c+d*x)]/d +
  Dist[a*n/d,Int[ArcCoth[a*x]^(n-1)*Log[2*c/(c+d*x)]/(1-a^2*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_./(x_*(c_+d_.*x_)),x_Symbol] :=
(Print["Int(10th)@InverseHyperbolicCotangentFunctions.m"];
  ArcCoth[a*x]^n*Log[2-2*c/(c+d*x)]/c -
  Dist[a*n/c,Int[ArcCoth[a*x]^(n-1)*Log[2-2*c/(c+d*x)]/(1-a^2*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_./(c_.*x_+d_.*x_^2),x_Symbol] :=
(Print["Int(11th)@InverseHyperbolicCotangentFunctions.m"];
  ArcCoth[a*x]^n*Log[2-2*c/(c+d*x)]/c -
  Dist[a*n/c,Int[ArcCoth[a*x]^(n-1)*Log[2-2*c/(c+d*x)]/(1-a^2*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_.*ArcCoth[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
(Print["Int(12th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/d,Int[x^(m-1)*ArcCoth[a*x]^n,x]] -
  Dist[c/d,Int[x^(m-1)*ArcCoth[a*x]^n/(c+d*x),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && RationalQ[m] && m>0 && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_*ArcCoth[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
(Print["Int(13th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/c,Int[x^m*ArcCoth[a*x]^n,x]] -
  Dist[d/c,Int[x^(m+1)*ArcCoth[a*x]^n/(c+d*x),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2-d^2] && RationalQ[m] && m<-1 && IntegerQ[n] && n>0

(* ::Code:: *)
Int[1/((c_+d_.*x_^2)*ArcCoth[a_.*x_]),x_Symbol] :=
(Print["Int(14th)@InverseHyperbolicCotangentFunctions.m"];
  Log[ArcCoth[a*x]]/(a*c)) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(15th)@InverseHyperbolicCotangentFunctions.m"];
  ArcCoth[a*x]^(n+1)/(a*c*(n+1))) /;
FreeQ[{a,c,d,n},x] && ZeroQ[a^2*c+d] && NonzeroQ[n+1]

(* ::Code:: *)
Int[x_*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(16th)@InverseHyperbolicCotangentFunctions.m"];
  ArcCoth[a*x]^(n+1)/(d*(n+1)) +
  Dist[1/(a*c),Int[ArcCoth[a*x]^n/(1-a*x),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_./(x_*(c_+d_.*x_^2)),x_Symbol] :=
(Print["Int(17th)@InverseHyperbolicCotangentFunctions.m"];
  ArcCoth[a*x]^(n+1)/(c*(n+1)) +
  Dist[1/c,Int[ArcCoth[a*x]^n/(x*(1+a*x)),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_./(c_.*x_+d_.*x_^3),x_Symbol] :=
(Print["Int(18th)@InverseHyperbolicCotangentFunctions.m"];
  ArcCoth[a*x]^(n+1)/(c*(n+1)) +
  Dist[1/c,Int[ArcCoth[a*x]^n/(x*(1+a*x)),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0

(* ::Code:: *)
Int[x_^m_*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(19th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/d,Int[x^(m-2)*ArcCoth[a*x]^n,x]] -
  Dist[c/d,Int[x^(m-2)*ArcCoth[a*x]^n/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n}] && m>1 && n>0

(* ::Code:: *)
Int[x_^m_*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(20th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/c,Int[x^m*ArcCoth[a*x]^n,x]] -
  Dist[d/c,Int[x^(m+2)*ArcCoth[a*x]^n/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n}] && m<-1 && n>0

(* ::Code:: *)
Int[x_^m_.*ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(21th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/(a^(m+1)*c),Subst[Int[x^n*Coth[x]^m,x],x,ArcCoth[a*x]]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n}] && (n<0 || Not[IntegerQ[n]]) && (IntegerQ[m] || PositiveQ[a])

(* ::Code:: *)
Int[x_^m_.*ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(22th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/(a*c),Subst[Int[x^n*(Coth[x]/a)^m,x],x,ArcCoth[a*x]]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n}] && (n<0 || Not[IntegerQ[n]]) && Not[IntegerQ[m] || PositiveQ[a]]

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_.*ArcCoth[u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(23th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/2,Int[ArcCoth[a*x]^n*Log[Regularize[1+1/u,x]]/(c+d*x^2),x]] -
  Dist[1/2,Int[ArcCoth[a*x]^n*Log[Regularize[1-1/u,x]]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && (ZeroQ[u^2-(1-2/(1+a*x))^2] || ZeroQ[u^2-(1-2/(1-a*x))^2])

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_.*Log[u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(24th)@InverseHyperbolicCotangentFunctions.m"];
  ArcCoth[a*x]^n*PolyLog[2,1-u]/(2*a*c) -
  Dist[n/2,Int[ArcCoth[a*x]^(n-1)*PolyLog[2,1-u]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1+a*x))^2]

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_.*Log[u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(25th)@InverseHyperbolicCotangentFunctions.m"];
  -ArcCoth[a*x]^n*PolyLog[2,1-u]/(2*a*c) +
  Dist[n/2,Int[ArcCoth[a*x]^(n-1)*PolyLog[2,1-u]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2/(1-a*x))^2]

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_.*PolyLog[p_,u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(26th)@InverseHyperbolicCotangentFunctions.m"];
  -ArcCoth[a*x]^n*PolyLog[p+1,u]/(2*a*c) +
  Dist[n/2,Int[ArcCoth[a*x]^(n-1)*PolyLog[p+1,u]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d,p},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1+a*x))^2]

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_.*PolyLog[p_,u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(27th)@InverseHyperbolicCotangentFunctions.m"];
  ArcCoth[a*x]^n*PolyLog[p+1,u]/(2*a*c) -
  Dist[n/2,Int[ArcCoth[a*x]^(n-1)*PolyLog[p+1,u]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d,p},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2/(1-a*x))^2]

(* ::Code:: *)
Int[ArcTanh[a_.*x_]^m_.*ArcCoth[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(28th)@InverseHyperbolicCotangentFunctions.m"];
  ArcTanh[a*x]^(m+1)*ArcCoth[a*x]^n/(a*c*(m+1)) -
  Dist[n/(m+1),Int[ArcTanh[a*x]^(m+1)*ArcCoth[a*x]^(n-1)/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n] && 0<n<m

(* ::Code:: *)
Int[ArcCoth[a_.*x_]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
(Print["Int(29th)@InverseHyperbolicCotangentFunctions.m"];
  -2*ArcCoth[a*x]*ArcTan[Sqrt[1-a*x]/Sqrt[1+a*x]]/(a*Sqrt[c]) - 
  I*PolyLog[2,-I*Sqrt[1-a*x]/Sqrt[1+a*x]]/(a*Sqrt[c]) + 
  I*PolyLog[2,I*Sqrt[1-a*x]/Sqrt[1+a*x]]/(a*Sqrt[c])) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && PositiveQ[c]

(* ::Code:: *)
Int[ArcCoth[a_.*x_]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
(Print["Int(30th)@InverseHyperbolicCotangentFunctions.m"];
  Sqrt[1-a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcCoth[a*x]/Sqrt[1-a^2*x^2],x]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && Not[PositiveQ[c]]

(* ::Code:: *)
Int[ArcCoth[a_.*x_]/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
(Print["Int(31th)@InverseHyperbolicCotangentFunctions.m"];
  -1/(a*c*Sqrt[c+d*x^2]) +
  x*ArcCoth[a*x]/(c*Sqrt[c+d*x^2])) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d]

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
(Print["Int(32th)@InverseHyperbolicCotangentFunctions.m"];
  -n*ArcCoth[a*x]^(n-1)/(a*c*Sqrt[c+d*x^2]) +
  x*ArcCoth[a*x]^n/(c*Sqrt[c+d*x^2]) +
  Dist[n*(n-1),Int[ArcCoth[a*x]^(n-2)/(c+d*x^2)^(3/2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n>1

(* ::Code:: *)
Int[ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
(Print["Int(33th)@InverseHyperbolicCotangentFunctions.m"];
  ArcCoth[a*x]^(n+1)/(a*c*(n+1)*Sqrt[c+d*x^2]) -
  x*ArcCoth[a*x]^(n+2)/(c*(n+1)*(n+2)*Sqrt[c+d*x^2]) +
  Dist[1/((n+1)*(n+2)),Int[ArcCoth[a*x]^(n+2)/(c+d*x^2)^(3/2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_.*ArcCoth[a_.*x_],x_Symbol] :=
(Print["Int(34th)@InverseHyperbolicCotangentFunctions.m"];
  (c+d*x^2)^m/(2*a*m*(2*m+1)) +
  x*(c+d*x^2)^m*ArcCoth[a*x]/(2*m+1) +
  Dist[2*c*m/(2*m+1),Int[(c+d*x^2)^(m-1)*ArcCoth[a*x],x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m] && m>0

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_*ArcCoth[a_.*x_],x_Symbol] :=
(Print["Int(35th)@InverseHyperbolicCotangentFunctions.m"];
  -(c+d*x^2)^(m+1)/(4*a*c*(m+1)^2) -
  x*(c+d*x^2)^(m+1)*ArcCoth[a*x]/(2*c*(m+1)) +
  Dist[(2*m+3)/(2*c*(m+1)),Int[(c+d*x^2)^(m+1)*ArcCoth[a*x],x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[m] && m<-1 && m!=-3/2

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_*ArcCoth[a_.*x_]^n_,x_Symbol] :=
(Print["Int(36th)@InverseHyperbolicCotangentFunctions.m"];
  -n*(c+d*x^2)^(m+1)*ArcCoth[a*x]^(n-1)/(4*a*c*(m+1)^2) -
  x*(c+d*x^2)^(m+1)*ArcCoth[a*x]^n/(2*c*(m+1)) +
  Dist[(2*m+3)/(2*c*(m+1)),Int[(c+d*x^2)^(m+1)*ArcCoth[a*x]^n,x]] +
  Dist[n*(n-1)/(4*(m+1)^2),Int[(c+d*x^2)^m*ArcCoth[a*x]^(n-2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n}] && m<-1 && m!=-3/2 && n>1

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_*ArcCoth[a_.*x_]^n_,x_Symbol] :=
(Print["Int(37th)@InverseHyperbolicCotangentFunctions.m"];
  (c+d*x^2)^(m+1)*ArcCoth[a*x]^(n+1)/(a*c*(n+1)) +
  Dist[2*a*(m+1)/(n+1),Int[x*(c+d*x^2)^m*ArcCoth[a*x]^(n+1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n}] && m<-1 && n<-1

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_*ArcCoth[a_.*x_]^n_,x_Symbol] :=
(Print["Int(38th)@InverseHyperbolicCotangentFunctions.m"];
  -Dist[(-c)^m/a,Subst[Int[x^n*Csch[x]^(2*(m+1)),x],x,ArcCoth[a*x]]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegerQ[m] && RationalQ[n] && m<-1 && (n<0 || Not[IntegerQ[n]])

(* ::Code:: *)
(* Int[(c_+d_.*x_^2)^m_*ArcCoth[a_.*x_]^n_,x_Symbol] :=
(Print["Int(39th)@InverseHyperbolicCotangentFunctions.m"];
  c^(m-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[(1-a^2*x^2)^m*ArcCoth[a*x]^n,x]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n}] && m<-1 && (n<0 || Not[IntegerQ[n]]) && IntegerQ[m-1/2] && Not[PositiveQ[c]] *)

(* ::Code:: *)
Int[x_*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(40th)@InverseHyperbolicCotangentFunctions.m"];
  (c+d*x^2)^(p+1)*ArcCoth[a*x]^n/(2*d*(p+1)) +
  Dist[n/(2*a*(p+1)),Int[(c+d*x^2)^p*ArcCoth[a*x]^(n-1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{n,p}] && n>0 && p!=-1

(* ::Code:: *)
Int[x_*(c_+d_.*x_^2)^p_./ArcCoth[a_.*x_]^2,x_Symbol] :=
(Print["Int(41th)@InverseHyperbolicCotangentFunctions.m"];
  -x*(c+d*x^2)^(p+1)/(a*c*ArcCoth[a*x]) +
  Dist[1/a,Int[(1-(2*p+3)*a^2*x^2)*(c+d*x^2)^p/ArcCoth[a*x],x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[p]

(* ::Code:: *)
Int[x_*ArcCoth[a_.*x_]^n_/(c_+d_.*x_^2)^2,x_Symbol] :=
(Print["Int(42th)@InverseHyperbolicCotangentFunctions.m"];
  x*ArcCoth[a*x]^(n+1)/(a*c*(n+1)*(c+d*x^2)) +
  (1+a^2*x^2)*ArcCoth[a*x]^(n+2)/(d*(n+1)*(n+2)*(c+d*x^2)) +
  Dist[4/((n+1)*(n+2)),Int[x*ArcCoth[a*x]^(n+2)/(c+d*x^2)^2,x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(43th)@InverseHyperbolicCotangentFunctions.m"];
  x^(m+1)*(c+d*x^2)^(p+1)*ArcCoth[a*x]^n/(c*(m+1)) -
  Dist[a*n/(m+1),Int[x^(m+1)*(c+d*x^2)^p*ArcCoth[a*x]^(n-1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && m<-1 && n>0 && ZeroQ[m+2*p+3]

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(44th)@InverseHyperbolicCotangentFunctions.m"];
  x^m*(c+d*x^2)^(p+1)*ArcCoth[a*x]^(n+1)/(a*c*(n+1)) -
  Dist[m/(a*(n+1)),Int[x^(m-1)*(c+d*x^2)^p*ArcCoth[a*x]^(n+1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && n<-1 && ZeroQ[m+2*p+2]

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(45th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/d,Int[x^(m-2)*(c+d*x^2)^(p+1)*ArcCoth[a*x]^n,x]] -
  Dist[c/d,Int[x^(m-2)*(c+d*x^2)^p*ArcCoth[a*x]^n,x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && m>1 && n!=-1 && p<-1

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(46th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/c,Int[x^m*(c+d*x^2)^(p+1)*ArcCoth[a*x]^n,x]] -
  Dist[d/c,Int[x^(m+2)*(c+d*x^2)^p*ArcCoth[a*x]^n,x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && m<0 && n!=-1 && p<-1

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(47th)@InverseHyperbolicCotangentFunctions.m"];
  x^(m+1)*(c+d*x^2)^(p+1)*ArcCoth[a*x]^n/(c*(m+1)) -
  Dist[a*n/(m+1),Int[x^(m+1)*(c+d*x^2)^p*ArcCoth[a*x]^(n-1),x]] +
  Dist[a^2*(m+2*p+3)/(m+1),Int[x^(m+2)*(c+d*x^2)^p*ArcCoth[a*x]^n,x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && m<-1 && n>0 && NonzeroQ[m+2*p+3]

(* ::Code:: *)
Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcCoth[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(48th)@InverseHyperbolicCotangentFunctions.m"];
  x^m*(c+d*x^2)^(p+1)*ArcCoth[a*x]^(n+1)/(a*c*(n+1)) -
  Dist[m/(a*(n+1)),Int[x^(m-1)*(c+d*x^2)^p*ArcCoth[a*x]^(n+1),x]] +
  Dist[a*(m+2*p+2)/(n+1),Int[x^(m+1)*(c+d*x^2)^p*ArcCoth[a*x]^(n+1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && IntegersQ[m,n,2*p] && n<-1 && NonzeroQ[m+2*p+2]

(* ::Code:: *)
Int[(e_.+f_.*x_^m_.)*(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_,x_Symbol] :=
(Print["Int(49th)@InverseHyperbolicCotangentFunctions.m"];
  -Dist[(-c)^p/a^(m+1),Subst[Int[Expand[x^n*TrigReduce[Regularize[(e*a^m+f*Coth[x]^m)*Csch[x]^(2*(p+1)),x]]],x],x,ArcCoth[a*x]]]) /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n}] && IntegerQ[p] && p<-1 && (n<0 || Not[IntegerQ[n]]) && (IntegerQ[m] || PositiveQ[a])

(* ::Code:: *)
Int[x_^m_.*(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_,x_Symbol] :=
(Print["Int(50th)@InverseHyperbolicCotangentFunctions.m"];
  -Dist[(-c)^p/a,Subst[Int[x^n*(Coth[x]/a)^m*Csch[x]^(2*(p+1)),x],x,ArcCoth[a*x]]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n}] && IntegerQ[p] && p<-1 && (n<0 || Not[IntegerQ[n]]) && Not[IntegerQ[m] || PositiveQ[a]]

(* ::Code:: *)
(* Int[x_^m_.*(c_+d_.*x_^2)^p_*ArcCoth[a_.*x_]^n_,x_Symbol] :=
(Print["Int(51th)@InverseHyperbolicCotangentFunctions.m"];
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1-a^2*x^2]*Int[x^m*(1-a^2*x^2)^p*ArcCoth[a*x]^n,x]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c+d] && RationalQ[{m,n,p}] && p<-1 && (n<0 || Not[IntegerQ[n]]) && IntegerQ[p-1/2] && Not[PositiveQ[c]] *)

(* ::Code:: *)
Int[ArcCoth[a_+b_.*x_],x_Symbol] :=
(Print["Int(52th)@InverseHyperbolicCotangentFunctions.m"];
  (a+b*x)*ArcCoth[a+b*x]/b + Log[1-(a+b*x)^2]/(2*b)) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[ArcCoth[a_+b_.*x_^n_],x_Symbol] :=
(Print["Int(53th)@InverseHyperbolicCotangentFunctions.m"];
  x*ArcCoth[a+b*x^n] -
  Dist[b*n,Int[x^n/(1-a^2-2*a*b*x^n-b^2*x^(2*n)),x]]) /;
FreeQ[{a,b},x] && RationalQ[n]

(* ::Code:: *)
Int[ArcCoth[a_.+b_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(54th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/2,Int[Log[1+1/(a+b*x^n)]/x,x]] -
  Dist[1/2,Int[Log[1-1/(a+b*x^n)]/x,x]]) /;
FreeQ[{a,b,n},x]

(* ::Code:: *)
Int[x_^m_.*ArcCoth[a_+b_.*x_^n_.],x_Symbol] :=
(Print["Int(55th)@InverseHyperbolicCotangentFunctions.m"];
  x^(m+1)*ArcCoth[a+b*x^n]/(m+1) -
  Dist[b*n/(m+1),Int[x^(m+n)/(1-a^2-2*a*b*x^n-b^2*x^(2*n)),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m+1!=0 && m+1!=n

(* ::Code:: *)
Int[ArcCoth[a_+b_.*x_]^n_.,x_Symbol] :=
(Print["Int(56th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/b,Subst[Int[ArcCoth[x]^n,x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1

(* ::Code:: *)
Int[x_^m_.*ArcCoth[a_+b_.*x_]^n_,x_Symbol] :=
(Print["Int(57th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/b^(m+1),Subst[Int[(x-a)^m*ArcCoth[x]^n,x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m>0 && n>1

(* ::Code:: *)
Int[ArcCoth[b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
(Print["Int(58th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/2,Int[Log[1+1/(b*x)]/(c+d*x^n),x]] -
  Dist[1/2,Int[Log[1-1/(b*x)]/(c+d*x^n),x]]) /;
FreeQ[{b,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[b^2*c+d]]

(* ::Code:: *)
Int[ArcCoth[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
(Print["Int(59th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/2,Int[Log[1+1/(a+b*x)]/(c+d*x^n),x]] -
  Dist[1/2,Int[Log[1-1/(a+b*x)]/(c+d*x^n),x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && Not[n==1 && ZeroQ[a*d-b*c]]

(* ::Code:: *)
Int[u_.*ArcCoth[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
(Print["Int(60th)@InverseHyperbolicCotangentFunctions.m"];
  Int[u*ArcTanh[a/c+b*x^n/c]^m,x]) /;
FreeQ[{a,b,c,n,m},x]

(* ::Code:: *)
If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
(Print["Int(61th)@InverseHyperbolicCotangentFunctions.m"];
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcCoth[a+b*x]]/(1-(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Coth[x]/b,x],x],x,ArcCoth[a+b*x]]/b",Hold[
  Dist[(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1],
	Subst[Int[Regularize[SubstForInverseFunction[u,tmp,x]*(-Csch[x]^2)^(n+1),x],x], x, tmp]]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCoth && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]]) /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
(Print["Int(62th)@InverseHyperbolicCotangentFunctions.m"];
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  Dist[(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1],
	Subst[Int[Regularize[SubstForInverseFunction[u,tmp,x]*(-Csch[x]^2)^(n+1),x],x], x, tmp]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcCoth && ZeroQ[Discriminant[v,x]*tmp[[1]]^2-D[v,x]^2]]) /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && PosQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]

(* ::Code:: *)
Int[u_.*E^(n_.*ArcCoth[v_]),x_Symbol] :=
(Print["Int(63th)@InverseHyperbolicCotangentFunctions.m"];
  Int[u*(1+v)^(n/2)/(-1+v)^(n/2),x]) /;
EvenQ[n]

(* ::Code:: *)
Int[E^(n_.*ArcCoth[v_]),x_Symbol] :=
(Print["Int(64th)@InverseHyperbolicCotangentFunctions.m"];
  Int[Expand[(1/Sqrt[1-1/v^2] + 1/(x*Sqrt[1-1/v^2]))^n],x]) /;
OddQ[n]

(* ::Code:: *)
Int[x_^m_.*E^(n_.*ArcCoth[v_]),x_Symbol] :=
(Print["Int(65th)@InverseHyperbolicCotangentFunctions.m"];
  Int[Expand[x^m*(1/Sqrt[1-1/v^2] + 1/(x*Sqrt[1-1/v^2]))^n],x]) /;
RationalQ[m] && OddQ[n]

(* ::Code:: *)
Int[E^(ArcCoth[a_.+b_.*x_]/2), x_Symbol] :=
(Print["Int(66th)@InverseHyperbolicCotangentFunctions.m"];
  x*E^(ArcCoth[a+b*x]/2) -
  Dist[b/2,Int[x*E^(ArcCoth[a+b*x]/2)/(1-(a+b*x)^2),x]]) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[x_^m_.*E^(ArcCoth[a_.+b_.*x_]/2), x_Symbol] :=
(Print["Int(67th)@InverseHyperbolicCotangentFunctions.m"];
  x^(m+1)*E^(ArcCoth[a+b*x]/2)/(m+1) -
  Dist[b/(2*(m+1)),Int[x^(m+1)*E^(ArcCoth[a+b*x]/2)/(1-(a+b*x)^2),x]]) /;
FreeQ[{a,b},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[u_.*E^(n_.*ArcCoth[v_])*(1-v_^2)^m_.,x_Symbol] :=
(Print["Int(68th)@InverseHyperbolicCotangentFunctions.m"];
  -(-1)^((n-1)/2)*v*Sqrt[1-1/v^2]/Sqrt[1-v^2]*Int[u*(1-v)^(m-n/2)*(1+v)^(m+n/2),x]) /;
OddQ[n] && IntegerQ[m-1/2]

(* ::Code:: *)
Int[u_.*E^ArcCoth[v_]*(a_+b_.*v_^2)^m_.,x_Symbol] :=
(Print["Int(69th)@InverseHyperbolicCotangentFunctions.m"];
  -Dist[a^m,Int[Expand[u*v*(1+v)*Sqrt[1-1/v^2]*(1-v^2)^(m-1),x],x]]) /;
FreeQ[{a,b},x] && ZeroQ[a+b] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[u_.*E^ArcCoth[v_]*(a_+b_.*v_^2)^m_.,x_Symbol] :=
(Print["Int(70th)@InverseHyperbolicCotangentFunctions.m"];
  (a+b*v^2)^m/(1-v^2)^m*Int[u*E^ArcCoth[v]*(1-v^2)^m,x]) /;
FreeQ[{a,b},x] && ZeroQ[a+b] && NonzeroQ[a-1]

(* ::Code:: *)
Int[u_.*E^(n_.*ArcCoth[v_])*(1-1/v_^2)^m_.,x_Symbol] :=
(Print["Int(71th)@InverseHyperbolicCotangentFunctions.m"];
  Int[u*(1+v)^(m+n/2)*(-1+v)^(m-n/2)/v^(2*m),x]) /;
IntegerQ[n] && IntegerQ[m-n/2]

(* ::Code:: *)
Int[u_.*E^(n_.*ArcCoth[v_])*(1-1/v_^2)^m_.,x_Symbol] :=
(Print["Int(72th)@InverseHyperbolicCotangentFunctions.m"];
  Int[Expand[u*(1+1/v)^n*(1-1/v^2)^(m-n/2),x],x]) /;
RationalQ[n] && IntegerQ[2*m]

(* ::Code:: *)
Int[u_.*E^ArcCoth[v_]*(a_+b_./v_^2)^m_.,x_Symbol] :=
(Print["Int(73th)@InverseHyperbolicCotangentFunctions.m"];
  (a+b/v^2)^m/(1-1/v^2)^m*Int[u*(1+1/v)*(1-1/v^2)^(m-1/2),x]) /;
FreeQ[{a,b},x] && ZeroQ[a+b] && IntegerQ[2*m]

(* ::Code:: *)
Int[ArcCoth[b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
(Print["Int(74th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/2,Int[Log[1+1/(b*f^(c+d*x))],x]] -
  Dist[1/2,Int[Log[1-1/(b*f^(c+d*x))],x]]) /;
FreeQ[{b,c,d,f},x] 

(* ::Code:: *)
Int[x_^m_.*ArcCoth[b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
(Print["Int(75th)@InverseHyperbolicCotangentFunctions.m"];
  Dist[1/2,Int[x^m*Log[1+1/(b*f^(c+d*x))],x]] -
  Dist[1/2,Int[x^m*Log[1-1/(b*f^(c+d*x))],x]]) /;
FreeQ[{b,c,d,f},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[ArcCoth[u_],x_Symbol] :=
(Print["Int(76th)@InverseHyperbolicCotangentFunctions.m"];
  x*ArcCoth[u] -
  Int[Regularize[x*D[u,x]/(1-u^2),x],x]) /;
InverseFunctionFreeQ[u,x]

(* ::Code:: *)
Int[x_^m_.*ArcCoth[u_],x_Symbol] :=
(Print["Int(77th)@InverseHyperbolicCotangentFunctions.m"];
  x^(m+1)*ArcCoth[u]/(m+1) -
  Dist[1/(m+1),Int[Regularize[x^(m+1)*D[u,x]/(1-u^2),x],x]]) /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	FalseQ[PowerVariableExpn[u,m+1,x]]

(* ::Code:: *)
Int[v_*ArcCoth[u_],x_Symbol] :=
(Print["Int(78th)@InverseHyperbolicCotangentFunctions.m"];
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  w*ArcCoth[u] -
  Int[Regularize[w*D[u,x]/(1-u^2),x],x] /;
 InverseFunctionFreeQ[w,x]]) /;
InverseFunctionFreeQ[u,x] && 
	Not[MatchQ[v, x^m_. /; FreeQ[m,x]]] &&
	FalseQ[FunctionOfLinear[v*ArcCoth[u],x]]
