(* ::Package:: *)

Int[Sin[c_.+d_.*x_]^j_.*(A_+B_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(1th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  B*x + Dist[A,Int[Sin[c+d*x]^j,x]]) /;
FreeQ[{c,d,A,B},x] && OneQ[j^2] && ZeroQ[j+k]

Int[Sqrt[Sin[c_.+d_.*x_]]*(A_+B_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(2th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[A,Int[Sqrt[Sin[c+d*x]],x]] + 
  Dist[B,Int[1/Sqrt[Sin[c+d*x]],x]]) /;
FreeQ[{c,d,A,B},x]

Int[(Sin[c_.+d_.*x_]^(-1))^m_*(A_.+B_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(3th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[Sin[c+d*x]^m*Csc[c+d*x]^m,Int[(A+B*Sin[c+d*x])/Sin[c+d*x]^m,x]]) /;
FreeQ[{c,d,A,B},x] && ZeroQ[m^2-1/4]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+B_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(4th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*Simplify[B*(j*k*m+(k+1)/2)+A*(j*k*m+(k+3)/2)*Sin[c+d*x]^k,x],x]]) /;
FreeQ[{c,d,A,B},x] && OneQ[j^2,k^2] && RationalQ[m] && j*k*m<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+B_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(5th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -B*Cos[c+d*x]*(Sin[c+d*x]^j)^m/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m-j*k)*(B*(j*k*m+(k-1)/2)+A*(j*k*m+(k+1)/2)*Sin[c+d*x]^k),x]]) /;
FreeQ[{c,d,A,B},x] && OneQ[j^2,k^2] && RationalQ[m] && j*k*m>0 && m^2!=1

Int[(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(6th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  (4*a*A+b*B*(k+1))*x/4 - (2*b*B*Cos[c+d*x]*Sin[c+d*x]^k)/(d*(k+3)) + (b*A+a*B)*Int[Sin[c+d*x]^k,x]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[k^2]

Int[(A_+B_.*Sin[c_.+d_.*x_]^k_.)/(a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(7th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  B*x/b) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[k^2] && ZeroQ[b*A-a*B]

Int[(A_.+B_.*Sin[c_.+d_.*x_])/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(8th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  B*x/b + Dist[(b*A-a*B)/b,Int[1/(a+b*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B]

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1))/(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(9th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  A*x/a - Dist[(b*A-a*B)/a,Int[1/(b+a*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B]

Int[(A_.+B_.*Sin[c_.+d_.*x_])/Sqrt[a_.+b_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(10th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[B/b,Int[Sqrt[a+b*Sin[c+d*x]],x]] +
  Dist[(b*A-a*B)/b,Int[1/Sqrt[a+b*Sin[c+d*x]],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B]

Int[(A_+B_.*Sin[c_.+d_.*x_]^(-1))/Sqrt[b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(11th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[1/(Sqrt[Sin[c+d*x]]*Sqrt[b*Csc[c+d*x]]),Int[(B+A*Sin[c+d*x])/Sqrt[Sin[c+d*x]],x]]) /;
FreeQ[{b,c,d,A,B},x]

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(12th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]]),
    Int[(B+A*Sin[c+d*x])*(b+a*Sin[c+d*x])^n/Sin[c+d*x]^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && IntegerQ[n-1/2] && -2<n<1

Int[(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_.+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(13th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[B/b,Int[(a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,n},x] && OneQ[k^2] && ZeroQ[b*A-a*B] && RationalQ[n] && n<0

Int[(A_+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(14th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  b*(b*A-a*B)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(a*(n+1)*(a^2-b^2)),
    Int[Simplify[A*(a^2-b^2)*(n+1)-(a*(b*A-a*B)*(n+1))*Sin[c+d*x]^(-1)+
        (b*(b*A-a*B)*(n+2))*Sin[c+d*x]^(-2),x]*
      (a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && n<-1

Int[(A_+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(15th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -b*B*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-1)/(d*n) + 
  Dist[1/n,
    Int[Simplify[a^2*A*n+(b^2*B*(n-1)+2*a*A*b*n+a^2*B*n)*Sin[c+d*x]^(-1)+
        (b*(b*A*n+a*B*(2*n-1)))*Sin[c+d*x]^(-2),x]*
      (a+b*Sin[c+d*x]^(-1))^(n-2),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && RationalQ[n] && n>1

Int[(A_+B_.*Sin[c_.+d_.*x_]^k_.)*(b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(16th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  2*A*Cos[c+d*x]*(b*Sin[c+d*x]^k)^(n+1)/(b*d*(2*n+k+1)) + 
  Dist[1/(b*(2*n+k+1)),
    Int[Simplify[B*(2*n+k+1)+A*(2*n+k+3)*Sin[c+d*x]^k,x]*(b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{b,c,d,A,B},x] && OneQ[k^2] && RationalQ[n] && n<-1

Int[(A_+B_.*Sin[c_.+d_.*x_]^k_.)*(b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(17th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -2*B*Cos[c+d*x]*(b*Sin[c+d*x]^k)^n/(d*(2*n+k+1)) + 
  Dist[1/(2*n+k+1),
    Int[Simplify[b*B*(2*n+k-1)+b*A*(2*n+k+1)*Sin[c+d*x]^k,x]*(b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{b,c,d,A,B},x] && OneQ[k^2] && RationalQ[n] && n>0

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sin[c_.+d_.*x_]*(a_+b_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(18th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[A/a,Int[1/Sin[c+d*x],x]] - 
  Dist[(b*A-a*B)/a,Int[1/(a+b*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[b*A-a*B]

Int[Sin[c_.+d_.*x_]^m_*(A_+B_.*Sin[c_.+d_.*x_])/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(19th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[B/b,Int[Sin[c+d*x]^m,x]] + 
  Dist[(b*A-a*B)/b,Int[Sin[c+d*x]^m/(a+b*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && ZeroQ[m^2-1/4]

Int[(A_+B_.*Sin[c_.+d_.*x_])*(a_+b_.*Sin[c_.+d_.*x_])^n_/Sin[c_.+d_.*x_],x_Symbol] :=
(Print["Int(20th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[B,Int[(a+b*Sin[c+d*x])^n,x]] + 
  Dist[A,Int[(a+b*Sin[c+d*x])^n/Sin[c+d*x],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[n^2-1/4]

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(21th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  B*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  (A-B)*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[A-B]

Int[(A_+B_.*Sin[c_.+d_.*x_])*Sqrt[a_.+b_.*Sin[c_.+d_.*x_]]/Sqrt[e_.+f_.*Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(22th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Int[(a*A+(b*A+a*B)*Sin[c+d*x]+b*B*Sin[c+d*x]^2)/(Sqrt[a+b*Sin[c+d*x]]*Sqrt[e+f*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d,e,f,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[e^2-f^2]

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(23th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  2*A*Sqrt[a+b*Sin[c+d*x]]*Tan[(c-Pi/2+d*x)/2]/(a*d*Sqrt[Sin[c+d*x]]) - 
  2*A/a*Int[Sqrt[a+b*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*(1+Sin[c+d*x])),x]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A+B]

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(24th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[A+B,Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]] + 
  Dist[A,Int[(1-Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[A+B]

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sqrt[Sin[c_.+d_.*x_]]*(a_+b_.*Sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
(Print["Int(25th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  2*A*(a-b)*Sqrt[Sin[c+d*x]]*Tan[(c-Pi/2+d*x)/2]/(a*d*(a+b)*Sqrt[a+b*Sin[c+d*x]]) + 
  Dist[2*A/(a*(a+b)),Int[Sqrt[a+b*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*(1+Sin[c+d*x])),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B]

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sqrt[Sin[c_.+d_.*x_]]*(a_+b_.*Sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
(Print["Int(26th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[(A-B)/(a-b),Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]] - 
  Dist[(b*A-a*B)/(a-b),Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && NonzeroQ[A-B]

Int[(A_+B_.*Sin[c_.+d_.*x_])*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]/Sin[c_.+d_.*x_]^(3/2),x_Symbol] :=
(Print["Int(27th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  (b*(A-B)+a*(A+B))*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Int[Simplify[a*A-(a*A-b*B)*Sin[c+d*x]+b*B*Sin[c+d*x]^2,x]/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2]

Int[Sqrt[Sin[c_.+d_.*x_]]*(A_+B_.*Sin[c_.+d_.*x_])/(a_+b_.*Sin[c_.+d_.*x_])^(3/2),x_Symbol] :=
(Print["Int(28th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  B/b*Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Dist[1/b,Int[Simplify[-a*B+(A*b-(a+b)*B)*Sin[c+d*x],x]/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B]

Int[Sin[c_.+d_.*x_]^m_.*(A_+B_.*Sin[c_.+d_.*x_]^k_.)*(b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(29th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[1/b^(k*m),Int[(A+B*Sin[c+d*x]^k)*(b*Sin[c+d*x]^k)^(k*m+n),x]]) /;
FreeQ[{b,c,d,A,B,n},x] && OneQ[k^2] && IntegerQ[m]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+B_.*Sin[c_.+d_.*x_]^k_.)*(b_*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(30th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[b^(n-1/2)*Sqrt[b*Sin[c+d*x]^k]/(Sqrt[Sin[c+d*x]^j])^(j*k),
    Int[Sin[c+d*x]^(j*m+k*n)*(A+B*Sin[c+d*x]^k),x]]) /;
FreeQ[{b,c,d,A,B},x] && OneQ[j^2,k^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && n>0

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+B_.*Sin[c_.+d_.*x_]^k_.)*(b_*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(31th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[b^(n+1/2)*(Sqrt[Sin[c+d*x]^j])^(j*k)/Sqrt[b*Sin[c+d*x]^k],
    Int[Sin[c+d*x]^(j*m+k*n)*(A+B*Sin[c+d*x]^k),x]]) /;
FreeQ[{b,c,d,A,B},x] && OneQ[j^2,k^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^(-1))/(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(32th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Int[(Sin[c+d*x]^j)^m*(B+A*Sin[c+d*x])/(b+a*Sin[c+d*x]),x]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2] && NonzeroQ[a^2-b^2] && RationalQ[m] && -1<m<=1

Int[Sin[c_.+d_.*x_]^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^(-1))*(a_.+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(33th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]]),
    Int[Sin[c+d*x]^(m-n-1)*(B+A*Sin[c+d*x])*(b+a*Sin[c+d*x])^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && IntegerQ[m] && IntegerQ[n-1/2] &&
  (m==1 && -1<n<1 || m==-1 && -2<n<0)

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^(-1))*(a_.+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(34th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/((Sqrt[Sin[c+d*x]^j])^j*Sqrt[a+b*Csc[c+d*x]]),
    Int[Sin[c+d*x]^(j*m-n-1)*(B+A*Sin[c+d*x])*(b+a*Sin[c+d*x])^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2] && NonzeroQ[a^2-b^2] && 
  IntegerQ[m-1/2] && IntegerQ[n-1/2] && -1<n<1 && 0<=j*m-n<=1

Int[(Sin[c_.+d_.*x_]^(-1))^m_*(A_.+B_.*Sin[c_.+d_.*x_])*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(35th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[Sqrt[Csc[c+d*x]]*Sqrt[Sin[c+d*x]],
    Int[(A+B*Sin[c+d*x])*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^m,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && IntegerQ[m-1/2] && RationalQ[n] && -1<m<2 && -2<n<1

Int[Sin[c_.+d_.*x_]*(A_+B_.*Sin[c_.+d_.*x_])*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(36th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  a*(b*A-a*B)*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) - 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[Simplify[b*(n+1)*(b*A-a*B)+(a^2*B-a*b*A*(n+2)+b^2*B*(n+1))*Sin[c+d*x],x]*
      (a+b*Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && n<-1

Int[Sin[c_.+d_.*x_]*(A_+B_.*Sin[c_.+d_.*x_])/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(37th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -B*Cos[c+d*x]/(b*d) + 
  Dist[(b*A-a*B)/b,Int[Sin[c+d*x]/(a+b*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[b*A-a*B]

Int[Sin[c_.+d_.*x_]*(A_+B_.*Sin[c_.+d_.*x_])*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(38th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -B*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+2)) + 
  Dist[1/(b*(n+2)),Int[Simplify[b*B*(n+1)-(a*B-b*A*(n+2))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && RationalQ[n] && n>-1 && n!=1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(39th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  a*A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[(b*A+a*B)*(j*k*m+(k+1)/2)+(a*A*(j*k*m+(k+3)/2)+b*B*(j*k*m+(k+1)/2))*Sin[c+d*x]^k,x],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && 
  RationalQ[m] && j*k*m+(k+1)/2!=0 && j*k*m<=-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(40th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -b*B*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+3)/2)) + 
  Dist[1/(j*k*m+(k+3)/2),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*A*(j*k*m+(k+3)/2)+b*B*(j*k*m+(k+1)/2)+(b*A+a*B)*(j*k*m+(k+3)/2)*Sin[c+d*x]^k,x],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && 
  RationalQ[m] && j*k*m>=-1

Int[(A_.+B_.*Sin[c_.+d_.*x_])*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(41th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -(b*A-a*B)*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) +
  Dist[1/((n+1)*(a^2-b^2)),
    Int[Simplify[(a*A-b*B)*(n+1)-(b*A-a*B)*(n+2)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && n<-1

Int[Sin[c_.+d_.*x_]^(-1)*(A_.+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(42th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -(b*A-a*B)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  Dist[1/((n+1)*(a^2-b^2)),
    Int[Sin[c+d*x]^(-1)*
      Simplify[(a*A-b*B)*(n+1)-(b*A-a*B)*(n+2)*Sin[c+d*x]^(-1),x]*(a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && n<-1

Int[(A_.+B_.*Sin[c_.+d_.*x_])*(a_.+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(43th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -B*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(n+1)) + 
  Dist[1/(n+1),
    Int[Simplify[b*B*n+a*A*(n+1)+(a*B*n+b*A*(n+1))*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && RationalQ[n] && n>0 && n!=1

Int[Sin[c_.+d_.*x_]^(-1)*(A_.+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(44th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -B*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  Dist[1/(n+1),
    Int[Sin[c+d*x]^(-1)*
      Simplify[b*B*n+a*A*(n+1)+(a*B*n+b*A*(n+1))*Sin[c+d*x]^(-1),x]*(a+b*Sin[c+d*x]^(-1))^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && RationalQ[n] && n>0 && n!=1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(45th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  Dist[B/b,Int[(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,m},x] && OneQ[j^2,k^2] && ZeroQ[b*A-a*B] && RationalQ[n] && n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(46th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  a*(b*A-a*B)*Cos[c+d*x]*(Sin[c+d*x]^j)^(m-j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(n+1)*(a^2-b^2)) - 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^(m-2*j*k)*
      Simplify[a*(b*A-a*B)*(j*k*m+(k-3)/2)+b*(b*A-a*B)*(n+1)*Sin[c+d*x]^k-
        (b*(a*A-b*B)*(n+1)+a*(b*A-a*B)*(j*k*m+(k-1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && j*k*m>1 && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(47th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -(b*A-a*B)*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n+1)/(d*(n+1)*(a^2-b^2)) + 
  Dist[1/((n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[(b*A-a*B)*(j*k*m+(k-1)/2)+(a*A-b*B)*(n+1)*Sin[c+d*x]^k-
        (b*A-a*B)*(j*k*m+n+(k+3)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && 0<j*k*m<1 && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(48th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -B*Cos[c+d*x]*(Sin[c+d*x]^j)^(m-j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(j*k*m+n+(k+1)/2)) + 
  Dist[1/(b*(j*k*m+n+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m-2*j*k)*
      Simplify[a*B*(j*k*m+(k-3)/2)+b*B*(j*k*m+n+(k-1)/2)*Sin[c+d*x]^k+
        (b*A*(n+1)+(b*A-a*B)*(j*k*m+(k-1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m>1 && -1<=n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(49th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -b*B*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-1)/(d*(j*k*m+n+(k+1)/2)) + 
  Dist[1/(j*k*m+n+(k+1)/2),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*(a*A*n+(a*A+b*B)*(j*k*m+(k+1)/2))+
        (a*(2*b*A+a*B)+(a^2*B+2*a*b*A+b^2*B)*(j*k*m+n+(k-1)/2))*Sin[c+d*x]^k+
        b*(a*B*(n-1)+(b*A+a*B)*(j*k*m+n+(k+1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-2),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m>=-1 && j*k*m!=1 && n>1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(50th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  -B*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+n+(k+1)/2)) + 
  Dist[1/(j*k*m+n+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[a*B*(j*k*m+(k-1)/2)+(a*A+(a*A+b*B)*(j*k*m+n+(k-1)/2))*Sin[c+d*x]^k+
        (n*(b*A+a*B)+b*A*(j*k*m+(k+1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m>0 && j*k*m!=1 && 0<n<1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(51th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  a*A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-1)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[a*((b*A+a*B)*(j*k*m+(k+1)/2)-b*A*(n-1))+
        (a^2*A+(a^2*A+2*a*b*B+b^2*A)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k+
        b*(a*A*n+(a*A+b*B)*(j*k*m+(k+1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-2),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m<-1 && n>1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(52th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[a*B*(j*k*m+(k+1)/2)-b*A*n+(a*A+(a*A+b*B)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k+
        b*A*(j*k*m+n+(k+3)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m<-1 && 0<n<=1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(53th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(a*d*(j*k*m+(k+1)/2)) + 
  Dist[1/(a*(j*k*m+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[(a*B-b*A)*(j*k*m+(k+1)/2)-b*A*(n+1)+a*A*(j*k*m+(k+3)/2)*Sin[c+d*x]^k+
        b*A*(j*k*m+n+(k+1)/2+2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m+(k+1)/2!=0 && j*k*m<=-1 && -1<=n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(54th)@(sin^j)^m (A+B sin^k) (a+b sin^k)^n.m"];
  b*(b*A-a*B)*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(a*(n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[A*(a^2-b^2)*(n+1)-b*(b*A-a*B)*(j*k*m+(k+1)/2)-a*(b*A-a*B)*(n+1)*Sin[c+d*x]^k+
        b*(b*A-a*B)*(j*k*m+n+(k+5)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && NonzeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && j*k*m<0 && n<-1
