(* ::Package:: *)

(* ::Code:: *)
Int[ArcTan[a_.*x_],x_Symbol] :=
(Print["Int(1th)@InverseTangentFunctions.m"];
  x*ArcTan[a*x] - Log[1+a^2*x^2]/(2*a)) /;
FreeQ[a,x]

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_,x_Symbol] :=
(Print["Int(2th)@InverseTangentFunctions.m"];
  x*ArcTan[a*x]^n -
  Dist[a*n,Int[x*ArcTan[a*x]^(n-1)/(1+a^2*x^2),x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>1

(* ::Code:: *)
Int[x_*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(3th)@InverseTangentFunctions.m"];
  ArcTan[a*x]^n/(2*a^2) + x^2*ArcTan[a*x]^n/2 -
  Dist[n/(2*a),Int[ArcTan[a*x]^(n-1),x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(4th)@InverseTangentFunctions.m"];
  x^(m-1)*ArcTan[a*x]^n/(a^2*(m+1)) + x^(m+1)*ArcTan[a*x]^n/(m+1) -
  Dist[n/(a*(m+1)),Int[x^(m-1)*ArcTan[a*x]^(n-1),x]] -
  Dist[(m-1)/(a^2*(m+1)),Int[x^(m-2)*ArcTan[a*x]^n,x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0 && RationalQ[m] && m>1

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_/x_,x_Symbol] :=
(Print["Int(5th)@InverseTangentFunctions.m"];
  2*ArcTan[a*x]^n*ArcTanh[1-2*I/(I-a*x)] -
  Dist[2*a*n,Int[ArcTan[a*x]^(n-1)*ArcTanh[1-2*I/(I-a*x)]/(1+a^2*x^2),x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>1

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_./x_^2,x_Symbol] :=
(Print["Int(6th)@InverseTangentFunctions.m"];
  -ArcTan[a*x]^n/x +
  Dist[a*n,Int[ArcTan[a*x]^(n-1)/(x*(1+a^2*x^2)),x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_./x_^3,x_Symbol] :=
(Print["Int(7th)@InverseTangentFunctions.m"];
  -a^2*ArcTan[a*x]^n/2 - ArcTan[a*x]^n/(2*x^2) +
  Dist[a*n/2,Int[ArcTan[a*x]^(n-1)/x^2,x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(8th)@InverseTangentFunctions.m"];
  x^(m+1)*ArcTan[a*x]^n/(m+1) + a^2*x^(m+3)*ArcTan[a*x]^n/(m+1) -
  Dist[a*n/(m+1),Int[x^(m+1)*ArcTan[a*x]^(n-1),x]] -
  Dist[a^2*(m+3)/(m+1),Int[x^(m+2)*ArcTan[a*x]^n,x]]) /;
FreeQ[a,x] && IntegerQ[n] && n>0 && RationalQ[m] && m<-3

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
(Print["Int(9th)@InverseTangentFunctions.m"];
  -ArcTan[a*x]^n*Log[2*c/(c+d*x)]/d +
  Dist[a*n/d,Int[ArcTan[a*x]^(n-1)*Log[2*c/(c+d*x)]/(1+a^2*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_./(x_*(c_+d_.*x_)),x_Symbol] :=
(Print["Int(10th)@InverseTangentFunctions.m"];
  ArcTan[a*x]^n*Log[2-2*c/(c+d*x)]/c -
  Dist[a*n/c,Int[ArcTan[a*x]^(n-1)*Log[2-2*c/(c+d*x)]/(1+a^2*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_./(c_.*x_+d_.*x_^2),x_Symbol] :=
(Print["Int(11th)@InverseTangentFunctions.m"];
  ArcTan[a*x]^n*Log[2-2*c/(c+d*x)]/c -
  Dist[a*n/c,Int[ArcTan[a*x]^(n-1)*Log[2-2*c/(c+d*x)]/(1+a^2*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_.*ArcTan[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
(Print["Int(12th)@InverseTangentFunctions.m"];
  Dist[1/d,Int[x^(m-1)*ArcTan[a*x]^n,x]] -
  Dist[c/d,Int[x^(m-1)*ArcTan[a*x]^n/(c+d*x),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && RationalQ[m] && m>0 && IntegerQ[n] && n>0

(* ::Code:: *)
Int[x_^m_*ArcTan[a_.*x_]^n_./(c_+d_.*x_),x_Symbol] :=
(Print["Int(13th)@InverseTangentFunctions.m"];
  Dist[1/c,Int[x^m*ArcTan[a*x]^n,x]] -
  Dist[d/c,Int[x^(m+1)*ArcTan[a*x]^n/(c+d*x),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[a^2*c^2+d^2] && RationalQ[m] && m<-1 && IntegerQ[n] && n>0

(* ::Code:: *)
Int[1/((c_+d_.*x_^2)*ArcTan[a_.*x_]),x_Symbol] :=
(Print["Int(14th)@InverseTangentFunctions.m"];
  Log[ArcTan[a*x]]/(a*c)) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(15th)@InverseTangentFunctions.m"];
  ArcTan[a*x]^(n+1)/(a*c*(n+1))) /;
FreeQ[{a,c,d,n},x] && ZeroQ[d-a^2*c] && NonzeroQ[n+1]

(* ::Code:: *)
Int[x_*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(16th)@InverseTangentFunctions.m"];
  -I*ArcTan[a*x]^(n+1)/(d*(n+1)) -
  Dist[1/(a*c),Int[ArcTan[a*x]^n/(I-a*x),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_./(x_*(c_+d_.*x_^2)),x_Symbol] :=
(Print["Int(17th)@InverseTangentFunctions.m"];
  -I*ArcTan[a*x]^(n+1)/(c*(n+1)) +
  Dist[I/c,Int[ArcTan[a*x]^n/(x*(I+a*x)),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_./(c_.*x_+d_.*x_^3),x_Symbol] :=
(Print["Int(18th)@InverseTangentFunctions.m"];
  -I*ArcTan[a*x]^(n+1)/(c*(n+1)) +
  Dist[I/c,Int[ArcTan[a*x]^n/(x*(I+a*x)),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0

(* ::Code:: *)
Int[x_^m_*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(19th)@InverseTangentFunctions.m"];
  Dist[1/d,Int[x^(m-2)*ArcTan[a*x]^n,x]] -
  Dist[c/d,Int[x^(m-2)*ArcTan[a*x]^n/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n}] && m>1 && n>0

(* ::Code:: *)
Int[x_^m_*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(20th)@InverseTangentFunctions.m"];
  Dist[1/c,Int[x^m*ArcTan[a*x]^n,x]] -
  Dist[d/c,Int[x^(m+2)*ArcTan[a*x]^n/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n}] && m<-1 && n>0

(* ::Code:: *)
Int[x_^m_.*ArcTan[a_.*x_]^n_/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(21th)@InverseTangentFunctions.m"];
  Dist[1/(a^(m+1)*c),Subst[Int[x^n*Tan[x]^m,x],x,ArcTan[a*x]]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n}] && (n<0 || Not[IntegerQ[n]]) && (IntegerQ[m] || PositiveQ[a])

(* ::Code:: *)
Int[x_^m_.*ArcTan[a_.*x_]^n_/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(22th)@InverseTangentFunctions.m"];
  Dist[1/(a*c),Subst[Int[x^n*(Tan[x]/a)^m,x],x,ArcTan[a*x]]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n}] && (n<0 || Not[IntegerQ[n]]) && Not[IntegerQ[m] || PositiveQ[a]]

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_.*ArcTanh[u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(23th)@InverseTangentFunctions.m"];
  Dist[1/2,Int[ArcTan[a*x]^n*Log[1+u]/(c+d*x^2),x]] -
  Dist[1/2,Int[ArcTan[a*x]^n*Log[1-u]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && (ZeroQ[u^2-(1-2*I/(I+a*x))^2] || ZeroQ[u^2-(1-2*I/(I-a*x))^2])

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_.*Log[u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(24th)@InverseTangentFunctions.m"];
  I*ArcTan[a*x]^n*PolyLog[2,1-u]/(2*a*c) -
  Dist[n*I/2,Int[ArcTan[a*x]^(n-1)*PolyLog[2,1-u]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I+a*x))^2]

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_.*Log[u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(25th)@InverseTangentFunctions.m"];
  -I*ArcTan[a*x]^n*PolyLog[2,1-u]/(2*a*c) +
  Dist[n*I/2,Int[ArcTan[a*x]^(n-1)*PolyLog[2,1-u]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[(1-u)^2-(1-2*I/(I-a*x))^2]

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_.*PolyLog[p_,u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(26th)@InverseTangentFunctions.m"];
  -I*ArcTan[a*x]^n*PolyLog[p+1,u]/(2*a*c) +
  Dist[n*I/2,Int[ArcTan[a*x]^(n-1)*PolyLog[p+1,u]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d,p},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I+a*x))^2]

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_.*PolyLog[p_,u_]/(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(27th)@InverseTangentFunctions.m"];
  I*ArcTan[a*x]^n*PolyLog[p+1,u]/(2*a*c) -
  Dist[n*I/2,Int[ArcTan[a*x]^(n-1)*PolyLog[p+1,u]/(c+d*x^2),x]]) /;
FreeQ[{a,c,d,p},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>0 && ZeroQ[u^2-(1-2*I/(I-a*x))^2]

(* ::Code:: *)
Int[1/(ArcCot[a_.*x_]*ArcTan[a_.*x_]*(c_+d_.*x_^2)),x_Symbol] :=
(Print["Int(28th)@InverseTangentFunctions.m"];
  (-Log[ArcCot[a*x]]+Log[ArcTan[a*x]])/(a*c*ArcCot[a*x]+a*c*ArcTan[a*x])) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]

(* ::Code:: *)
Int[ArcCot[a_.*x_]^m_.*ArcTan[a_.*x_]^n_./(c_+d_.*x_^2),x_Symbol] :=
(Print["Int(29th)@InverseTangentFunctions.m"];
  -ArcCot[a*x]^(m+1)*ArcTan[a*x]^n/(a*c*(m+1)) +
  Dist[n/(m+1),Int[ArcCot[a*x]^(m+1)*ArcTan[a*x]^(n-1)/(c+d*x^2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n] && 0<n<=m

(* ::Code:: *)
Int[ArcTan[a_.*x_]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
(Print["Int(30th)@InverseTangentFunctions.m"];
  -2*I*ArcTan[a*x]*ArcTan[Sqrt[1+I*a*x]/Sqrt[1-I*a*x]]/(a*Sqrt[c]) + 
  I*PolyLog[2,-I*Sqrt[1+I*a*x]/Sqrt[1-I*a*x]]/(a*Sqrt[c]) -
  I*PolyLog[2,I*Sqrt[1+I*a*x]/Sqrt[1-I*a*x]]/(a*Sqrt[c])) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && PositiveQ[c]

(* ::Code:: *)
Int[ArcTan[a_.*x_]/Sqrt[c_+d_.*x_^2],x_Symbol] :=
(Print["Int(31th)@InverseTangentFunctions.m"];
  Sqrt[1+a^2*x^2]/Sqrt[c+d*x^2]*Int[ArcTan[a*x]/Sqrt[1+a^2*x^2],x]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && Not[PositiveQ[c]]

(* ::Code:: *)
Int[ArcTan[a_.*x_]/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
(Print["Int(32th)@InverseTangentFunctions.m"];
  1/(a*c*Sqrt[c+d*x^2]) +
  x*ArcTan[a*x]/(c*Sqrt[c+d*x^2])) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c]

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
(Print["Int(33th)@InverseTangentFunctions.m"];
  n*ArcTan[a*x]^(n-1)/(a*c*Sqrt[c+d*x^2]) +
  x*ArcTan[a*x]^n/(c*Sqrt[c+d*x^2]) -
  Dist[n*(n-1),Int[ArcTan[a*x]^(n-2)/(c+d*x^2)^(3/2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n>1

(* ::Code:: *)
Int[ArcTan[a_.*x_]^n_/(c_+d_.*x_^2)^(3/2),x_Symbol] :=
(Print["Int(34th)@InverseTangentFunctions.m"];
  ArcTan[a*x]^(n+1)/(a*c*(n+1)*Sqrt[c+d*x^2]) +
  x*ArcTan[a*x]^(n+2)/(c*(n+1)*(n+2)*Sqrt[c+d*x^2]) -
  Dist[1/((n+1)*(n+2)),Int[ArcTan[a*x]^(n+2)/(c+d*x^2)^(3/2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_.*ArcTan[a_.*x_],x_Symbol] :=
(Print["Int(35th)@InverseTangentFunctions.m"];
  -(c+d*x^2)^m/(2*a*m*(2*m+1)) +
  x*(c+d*x^2)^m*ArcTan[a*x]/(2*m+1) +
  Dist[2*c*m/(2*m+1),Int[(c+d*x^2)^(m-1)*ArcTan[a*x],x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m] && m>0

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_*ArcTan[a_.*x_],x_Symbol] :=
(Print["Int(36th)@InverseTangentFunctions.m"];
  (c+d*x^2)^(m+1)/(4*a*c*(m+1)^2) -
  x*(c+d*x^2)^(m+1)*ArcTan[a*x]/(2*c*(m+1)) +
  Dist[(2*m+3)/(2*c*(m+1)),Int[(c+d*x^2)^(m+1)*ArcTan[a*x],x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[m] && m<-1 && m!=-3/2

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_*ArcTan[a_.*x_]^n_,x_Symbol] :=
(Print["Int(37th)@InverseTangentFunctions.m"];
  n*(c+d*x^2)^(m+1)*ArcTan[a*x]^(n-1)/(4*a*c*(m+1)^2) -
  x*(c+d*x^2)^(m+1)*ArcTan[a*x]^n/(2*c*(m+1)) +
  Dist[(2*m+3)/(2*c*(m+1)),Int[(c+d*x^2)^(m+1)*ArcTan[a*x]^n,x]] -
  Dist[n*(n-1)/(4*(m+1)^2),Int[(c+d*x^2)^m*ArcTan[a*x]^(n-2),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n}] && m<-1 && m!=-3/2 && n>1

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_*ArcTan[a_.*x_]^n_,x_Symbol] :=
(Print["Int(38th)@InverseTangentFunctions.m"];
  (c+d*x^2)^(m+1)*ArcTan[a*x]^(n+1)/(a*c*(n+1)) -
  Dist[2*a*(m+1)/(n+1),Int[x*(c+d*x^2)^m*ArcTan[a*x]^(n+1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n}] && m<-1 && n<-1

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_*ArcTan[a_.*x_]^n_,x_Symbol] :=
(Print["Int(39th)@InverseTangentFunctions.m"];
  Dist[c^m/a,Subst[Int[x^n*Sec[x]^(2*(m+1)),x],x,ArcTan[a*x]]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n}] && m<-1 && (n<0 || Not[IntegerQ[n]]) && (IntegerQ[m] || PositiveQ[c])

(* ::Code:: *)
Int[(c_+d_.*x_^2)^m_*ArcTan[a_.*x_]^n_,x_Symbol] :=
(Print["Int(40th)@InverseTangentFunctions.m"];
  c^(m-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[(1+a^2*x^2)^m*ArcTan[a*x]^n,x]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n}] && m<-1 && (n<0 || Not[IntegerQ[n]]) && IntegerQ[m-1/2] && Not[PositiveQ[c]]

(* ::Code:: *)
Int[x_*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(41th)@InverseTangentFunctions.m"];
  (c+d*x^2)^(p+1)*ArcTan[a*x]^n/(2*d*(p+1)) -
  Dist[n/(2*a*(p+1)),Int[(c+d*x^2)^p*ArcTan[a*x]^(n-1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{n,p}] && n>0 && p!=-1

(* ::Code:: *)
Int[x_*(c_+d_.*x_^2)^p_./ArcTan[a_.*x_]^2,x_Symbol] :=
(Print["Int(42th)@InverseTangentFunctions.m"];
  -x*(c+d*x^2)^(p+1)/(a*c*ArcTan[a*x]) +
  Dist[1/a,Int[(1+(2*p+3)*a^2*x^2)*(c+d*x^2)^p/ArcTan[a*x],x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[p]

(* ::Code:: *)
Int[x_*ArcTan[a_.*x_]^n_/(c_+d_.*x_^2)^2,x_Symbol] :=
(Print["Int(43th)@InverseTangentFunctions.m"];
  x*ArcTan[a*x]^(n+1)/(a*c*(n+1)*(c+d*x^2)) -
  (1-a^2*x^2)*ArcTan[a*x]^(n+2)/(d*(n+1)*(n+2)*(c+d*x^2)) -
  Dist[4/((n+1)*(n+2)),Int[x*ArcTan[a*x]^(n+2)/(c+d*x^2)^2,x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[n] && n<-1 && n!=-2

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(44th)@InverseTangentFunctions.m"];
  x^(m+1)*(c+d*x^2)^(p+1)*ArcTan[a*x]^n/(c*(m+1)) -
  Dist[a*n/(m+1),Int[x^(m+1)*(c+d*x^2)^p*ArcTan[a*x]^(n-1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && m<-1 && n>0 && ZeroQ[m+2*p+3]

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(45th)@InverseTangentFunctions.m"];
  x^m*(c+d*x^2)^(p+1)*ArcTan[a*x]^(n+1)/(a*c*(n+1)) -
  Dist[m/(a*(n+1)),Int[x^(m-1)*(c+d*x^2)^p*ArcTan[a*x]^(n+1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && n<-1 && ZeroQ[m+2*p+2]

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(46th)@InverseTangentFunctions.m"];
  Dist[1/d,Int[x^(m-2)*(c+d*x^2)^(p+1)*ArcTan[a*x]^n,x]] -
  Dist[c/d,Int[x^(m-2)*(c+d*x^2)^p*ArcTan[a*x]^n,x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && m>1 && n!=-1 && p<-1

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(47th)@InverseTangentFunctions.m"];
  Dist[1/c,Int[x^m*(c+d*x^2)^(p+1)*ArcTan[a*x]^n,x]] -
  Dist[d/c,Int[x^(m+2)*(c+d*x^2)^p*ArcTan[a*x]^n,x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && m<0 && n!=-1 && p<-1

(* ::Code:: *)
Int[x_^m_*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(48th)@InverseTangentFunctions.m"];
  x^(m+1)*(c+d*x^2)^(p+1)*ArcTan[a*x]^n/(c*(m+1)) -
  Dist[a*n/(m+1),Int[x^(m+1)*(c+d*x^2)^p*ArcTan[a*x]^(n-1),x]] -
  Dist[a^2*(m+2*p+3)/(m+1),Int[x^(m+2)*(c+d*x^2)^p*ArcTan[a*x]^n,x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && m<-1 && n>0 && NonzeroQ[m+2*p+3]

(* ::Code:: *)
Int[x_^m_.*(c_+d_.*x_^2)^p_.*ArcTan[a_.*x_]^n_.,x_Symbol] :=
(Print["Int(49th)@InverseTangentFunctions.m"];
  x^m*(c+d*x^2)^(p+1)*ArcTan[a*x]^(n+1)/(a*c*(n+1)) -
  Dist[m/(a*(n+1)),Int[x^(m-1)*(c+d*x^2)^p*ArcTan[a*x]^(n+1),x]] -
  Dist[a*(m+2*p+2)/(n+1),Int[x^(m+1)*(c+d*x^2)^p*ArcTan[a*x]^(n+1),x]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && IntegersQ[m,n,2*p] && n<-1 && NonzeroQ[m+2*p+2]

(* ::Code:: *)
Int[(e_.+f_.*x_^m_.)*(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_,x_Symbol] :=
(Print["Int(50th)@InverseTangentFunctions.m"];
  Dist[c^p/a^(m+1),Subst[Int[Expand[x^n*TrigReduce[Regularize[(e*a^m+f*Tan[x]^m)*Sec[x]^(2*(p+1)),x]]],x],x,ArcTan[a*x]]]) /;
FreeQ[{a,c,d,e,f},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n,p}] && p<-1 && (n<0 || Not[IntegerQ[n]]) && (IntegerQ[p] || PositiveQ[c]) && (IntegerQ[m] || PositiveQ[a])

(* ::Code:: *)
Int[x_^m_.*(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_,x_Symbol] :=
(Print["Int(51th)@InverseTangentFunctions.m"];
  Dist[c^p/a,Subst[Int[x^n*(Tan[x]/a)^m*Sec[x]^(2*(p+1)),x],x,ArcTan[a*x]]]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n,p}] && p<-1 && (n<0 || Not[IntegerQ[n]]) && (IntegerQ[p] || PositiveQ[c]) && Not[IntegerQ[m] || PositiveQ[a]]

(* ::Code:: *)
Int[x_^m_.*(c_+d_.*x_^2)^p_*ArcTan[a_.*x_]^n_,x_Symbol] :=
(Print["Int(52th)@InverseTangentFunctions.m"];
  c^(p-1/2)*Sqrt[c+d*x^2]/Sqrt[1+a^2*x^2]*Int[x^m*(1+a^2*x^2)^p*ArcTan[a*x]^n,x]) /;
FreeQ[{a,c,d},x] && ZeroQ[d-a^2*c] && RationalQ[{m,n,p}] && p<-1 && (n<0 || Not[IntegerQ[n]]) && IntegerQ[p-1/2] && Not[PositiveQ[c]]

(* ::Code:: *)
Int[ArcTan[a_+b_.*x_],x_Symbol] :=
(Print["Int(53th)@InverseTangentFunctions.m"];
  (a+b*x)*ArcTan[a+b*x]/b - Log[1+(a+b*x)^2]/(2*b)) /;
FreeQ[{a,b},x]

(* ::Code:: *)
Int[ArcTan[a_+b_.*x_^n_],x_Symbol] :=
(Print["Int(54th)@InverseTangentFunctions.m"];
  x*ArcTan[a+b*x^n] -
  Dist[b*n,Int[x^n/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x]]) /;
FreeQ[{a,b},x] && RationalQ[n]

(* ::Code:: *)
Int[ArcTan[a_.+b_.*x_^n_.]/x_,x_Symbol] :=
(Print["Int(55th)@InverseTangentFunctions.m"];
  Dist[I/2,Int[Log[1-I*a-I*b*x^n]/x,x]] -
  Dist[I/2,Int[Log[1+I*a+I*b*x^n]/x,x]]) /;
FreeQ[{a,b,n},x]

(* ::Code:: *)
Int[x_^m_.*ArcTan[a_+b_.*x_^n_.],x_Symbol] :=
(Print["Int(56th)@InverseTangentFunctions.m"];
  x^(m+1)*ArcTan[a+b*x^n]/(m+1) -
  Dist[b*n/(m+1),Int[x^(m+n)/(1+a^2+2*a*b*x^n+b^2*x^(2*n)),x]]) /;
FreeQ[{a,b},x] && RationalQ[{m,n}] && m+1!=0 && m+1!=n

(* ::Code:: *)
Int[ArcTan[a_+b_.*x_]^n_,x_Symbol] :=
(Print["Int(57th)@InverseTangentFunctions.m"];
  Dist[1/b,Subst[Int[ArcTan[x]^n,x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegerQ[n] && n>1

(* ::Code:: *)
Int[x_^m_.*ArcTan[a_+b_.*x_]^n_,x_Symbol] :=
(Print["Int(58th)@InverseTangentFunctions.m"];
  Dist[1/b^(m+1),Subst[Int[(x-a)^m*ArcTan[x]^n,x],x,a+b*x]]) /;
FreeQ[{a,b},x] && IntegersQ[m,n] && m>0 && n>1

(* ::Code:: *)
Int[ArcTan[b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
(Print["Int(59th)@InverseTangentFunctions.m"];
  Dist[I/2,Int[Log[1-I*b*x]/(c+d*x^n),x]] -
  Dist[I/2,Int[Log[1+I*b*x]/(c+d*x^n),x]]) /;
FreeQ[{b,c,d},x] && IntegerQ[n] && Not[n==2 && ZeroQ[d-b^2*c]]

(* ::Code:: *)
Int[ArcTan[a_+b_.*x_]/(c_+d_.*x_^n_.),x_Symbol] :=
(Print["Int(60th)@InverseTangentFunctions.m"];
  Dist[I/2,Int[Log[1-I*a-I*b*x]/(c+d*x^n),x]] -
  Dist[I/2,Int[Log[1+I*a+I*b*x]/(c+d*x^n),x]]) /;
FreeQ[{a,b,c,d},x] && IntegerQ[n] && Not[n==1 && ZeroQ[a*d-b*c]]

(* ::Code:: *)
Int[u_.*ArcTan[c_./(a_.+b_.*x_^n_.)]^m_.,x_Symbol] :=
(Print["Int(61th)@InverseTangentFunctions.m"];
  Int[u*ArcCot[a/c+b*x^n/c]^m,x]) /;
FreeQ[{a,b,c,n,m},x]

(* ::Code:: *)
If[ShowSteps,

Int[u_*v_^n_.,x_Symbol] :=
(Print["Int(62th)@InverseTangentFunctions.m"];
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  ShowStep["","Int[f[x,ArcTan[a+b*x]]/(1+(a+b*x)^2),x]",
		   "Subst[Int[f[-a/b+Tan[x]/b,x],x],x,ArcTan[a+b*x]]/b",Hold[
  Dist[(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1],
	Subst[Int[Regularize[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp]]]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTan && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]]) /;
SimplifyFlag && QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]],

Int[u_*v_^n_.,x_Symbol] :=
(Print["Int(63th)@InverseTangentFunctions.m"];
  Module[{tmp=InverseFunctionOfLinear[u,x]},
  Dist[(-Discriminant[v,x]/(4*Coefficient[v,x,2]))^n/Coefficient[tmp[[1]],x,1],
	Subst[Int[Regularize[SubstForInverseFunction[u,tmp,x]*Sec[x]^(2*(n+1)),x],x], x, tmp]] /;
 NotFalseQ[tmp] && Head[tmp]===ArcTan && ZeroQ[Discriminant[v,x]*tmp[[1]]^2+D[v,x]^2]]) /;
QuadraticQ[v,x] && IntegerQ[n] && n<0 && NegQ[Discriminant[v,x]] && MatchQ[u,r_.*f_^w_ /; FreeQ[f,x]]]

(* ::Code:: *)
Int[ArcTan[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
(Print["Int(64th)@InverseTangentFunctions.m"];
  Dist[I/2,Int[Log[1-I*a-I*b*f^(c+d*x)],x]] -
  Dist[I/2,Int[Log[1+I*a+I*b*f^(c+d*x)],x]]) /;
FreeQ[{a,b,c,d,f},x]

(* ::Code:: *)
Int[x_^m_.*ArcTan[a_.+b_.*f_^(c_.+d_.*x_)],x_Symbol] :=
(Print["Int(65th)@InverseTangentFunctions.m"];
  Dist[I/2,Int[x^m*Log[1-I*a-I*b*f^(c+d*x)],x]] -
  Dist[I/2,Int[x^m*Log[1+I*a+I*b*f^(c+d*x)],x]]) /;
FreeQ[{a,b,c,d,f},x] && IntegerQ[m] && m>0

(* ::Code:: *)
Int[ArcTan[u_],x_Symbol] :=
(Print["Int(66th)@InverseTangentFunctions.m"];
  x*ArcTan[u] -
  Int[Regularize[x*D[u,x]/(1+u^2),x],x]) /;
InverseFunctionFreeQ[u,x]

(* ::Code:: *)
Int[x_^m_.*ArcTan[u_],x_Symbol] :=
(Print["Int(67th)@InverseTangentFunctions.m"];
  x^(m+1)*ArcTan[u]/(m+1) -
  Dist[1/(m+1),Int[Regularize[x^(m+1)*D[u,x]/(1+u^2),x],x]]) /;
FreeQ[m,x] && NonzeroQ[m+1] && InverseFunctionFreeQ[u,x] && 
	Not[FunctionOfQ[x^(m+1),u,x]] && 
	FalseQ[PowerVariableExpn[u,m+1,x]]

(* ::Code:: *)
Int[v_*ArcTan[u_],x_Symbol] :=
(Print["Int(68th)@InverseTangentFunctions.m"];
  Module[{w=Block[{ShowSteps=False,StepCounter=Null}, Int[v,x]]},  
  w*ArcTan[u] -
  Int[Regularize[w*D[u,x]/(1+u^2),x],x] /;
 InverseFunctionFreeQ[w,x]]) /;
InverseFunctionFreeQ[u,x] && 
	Not[MatchQ[v, x^m_. /; FreeQ[m,x]]] &&
	FalseQ[FunctionOfLinear[v*ArcTan[u],x]]
