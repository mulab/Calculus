(* ::Package:: *)

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+C_.*Sin[c_.+d_.*x_]^k2_),x_Symbol] :=
(Print["Int(1th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k2/2)/(d*(j*k2/2*m+(k2/2+1)/2))) /;
FreeQ[{c,d,A,C,m},x] && OneQ[j^2,k2^2/4] && ZeroQ[A+(A+C)*(j*k2/2*m+(k2/2+1)/2)]

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_),x_Symbol] :=
(Print["Int(2th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*Simplify[B*(j*k*m+(k+1)/2)+(A+(A+C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k,x],x]]) /;
FreeQ[{c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && RationalQ[m] && j*k*m+(k+1)/2!=0 && j*k*m<=-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_+C_.*Sin[c_.+d_.*x_]^k2_),x_Symbol] :=
(Print["Int(3th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k2/2)/(d*(j*k2/2*m+(k2/2+1)/2)) + 
  Dist[(A+(A+C)*(j*k2/2*m+(k2/2+1)/2))/(j*k2/2*m+(k2/2+1)/2),Int[(Sin[c+d*x]^j)^(m+j*k2),x]]) /;
FreeQ[{c,d,A,C},x] && OneQ[j^2,k2^2/4] && RationalQ[m] && j*k2/2*m+(k2/2+1)/2!=0 && j*k2/2*m<=-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_),x_Symbol] :=
(Print["Int(4th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+3)/2)) + 
  Dist[1/(j*k*m+(k+3)/2),
    Int[(Sin[c+d*x]^j)^m*Simplify[A+(A+C)*(j*k*m+(k+1)/2)+B*(j*k*m+(k+3)/2)*Sin[c+d*x]^k,x],x]]) /;
FreeQ[{c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && RationalQ[m] && j*k*m+(k+3)/2!=0 && j*k*m>=-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_+C_.*Sin[c_.+d_.*x_]^k2_),x_Symbol] :=
(Print["Int(5th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k2/2)/(d*(j*k2/2*m+(k2/2+3)/2)) + 
  Dist[(A+(A+C)*(j*k2/2*m+(k2/2+1)/2))/(j*k2/2*m+(k2/2+3)/2),Int[(Sin[c+d*x]^j)^m,x]]) /;
FreeQ[{c,d,A,C},x] && OneQ[j^2,k2^2/4] && RationalQ[m] && j*k2/2*m+(k2/2+3)/2!=0 && j*k2/2*m>=-1

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(6th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]/(b*d) + Dist[1/b,Int[(b*A+(b*B-a*C)*Sin[c+d*x])/(a+b*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x]

Int[(A_+C_.*Sin[c_.+d_.*x_]^2)/(a_+b_.*Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(7th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]/(b*d) + Dist[1/b,Int[(b*A-a*C*Sin[c+d*x])/(a+b*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,C},x]

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))/(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(8th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*x/a + Int[(C+(B-b*A/a)*Sin[c+d*x])/(Sin[c+d*x]*(b+a*Sin[c+d*x])),x]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]

Int[(A_+C_.*Sin[c_.+d_.*x_]^(-2))/(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(9th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*x/a + Int[(C-b*A/a*Sin[c+d*x])/(Sin[c+d*x]*(b+a*Sin[c+d*x])),x]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]

Int[(A_+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))*(b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(10th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sin[c+d*x]^n*(b*Csc[c+d*x])^n,Int[(C+B*Sin[c+d*x]+A*Sin[c+d*x]^2)/Sin[c+d*x]^(n+2),x]]) /;
FreeQ[{b,c,d,A,B,C},x] && ZeroQ[n^2-1/4]

Int[(A_+C_.*Sin[c_.+d_.*x_]^(-2))*(b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(11th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sin[c+d*x]^n*(b*Csc[c+d*x])^n,Int[(C+A*Sin[c+d*x]^2)/Sin[c+d*x]^(n+2),x]]) /;
FreeQ[{b,c,d,A,C},x] && ZeroQ[n^2-1/4]

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_+d_.*x_]^(-2))*(a_.+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(12th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]]),
    Int[(C+B*Sin[c+d*x]+A*Sin[c+d*x]^2)*(b+a*Sin[c+d*x])^n/Sin[c+d*x]^(n+2),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && IntegerQ[n-1/2] && -2<n<0

Int[(A_.+C_.*Sin[c_.+d_.*x_]^(-2))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(13th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]]),
    Int[(C+A*Sin[c+d*x]^2)*(b+a*Sin[c+d*x])^n/Sin[c+d*x]^(n+2),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && IntegerQ[n-1/2] && -2<n<0

Int[(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(14th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[1/b^2,Int[Simplify[b*B-a*C+b*C*Sin[c+d*x]^k,x]*(a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[k^2] && k2===2*k && ZeroQ[a^2*C-a*b*B+b^2*A] && RationalQ[n] && 
  n<-1

Int[(A_+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(15th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[C/b^2,Int[Simplify[-a+b*Sin[c+d*x]^k,x]*(a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[k^2] && k2===2*k && ZeroQ[a^2*C+b^2*A] && RationalQ[n] && n<-1

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(16th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  (a^2*C-a*b*B+b^2*A)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(a*(n+1)*(a^2-b^2)),
    Int[Simplify[A*(a^2-b^2)*(n+1)-(a*(b*A-a*B+b*C)*(n+1))*Sin[c+d*x]^(-1)+
        (a^2*C-a*b*B+b^2*A)*(n+2)*Sin[c+d*x]^(-2),x]*
      (a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && NonzeroQ[a^2*C-a*b*B+b^2*A] && RationalQ[n] && n<-1

Int[(A_.+C_.*Sin[c_.+d_.*x_]^(-2))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(17th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  (a^2*C+b^2*A)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(a*(n+1)*(a^2-b^2)),
    Int[Simplify[A*(a^2-b^2)*(n+1)-(a*b*(A+C)*(n+1))*Sin[c+d*x]^(-1)+(a^2*C+b^2*A)*(n+2)*Sin[c+d*x]^(-2),x]*
      (a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && NonzeroQ[a^2*C+b^2*A] && RationalQ[n] && n<-1

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_.,x_Symbol] :=
(Print["Int(18th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  Dist[1/(n+1),
    Int[Simplify[a*A*(n+1)+(b*A+a*B+n*(b*A+a*B+b*C))*Sin[c+d*x]^(-1)+(a*C*n+b*B*(n+1))*Sin[c+d*x]^(-2),x]*
      (a+b*Sin[c+d*x]^(-1))^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && RationalQ[n] && n>0

Int[(A_.+C_.*Sin[c_.+d_.*x_]^(-2))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_.,x_Symbol] :=
(Print["Int(19th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  Dist[1/(n+1),
    Int[Simplify[a*A*(n+1)+b*(A+n*(A+C))*Sin[c+d*x]^(-1)+a*C*n*Sin[c+d*x]^(-2),x]*
      (a+b*Sin[c+d*x]^(-1))^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && RationalQ[n] && n>0 && Not[ZeroQ[A] && ZeroQ[a^2-b^2]]

Int[(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*(b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(20th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  2*A*Cos[c+d*x]*(b*Sin[c+d*x]^k)^(n+1)/(b*d*(2*n+k+1)) + 
  Dist[1/(b*(2*n+k+1)),
    Int[Simplify[(2*n+k+1)*B+(2*A+(A+C)*(2*n+k+1))*Sin[c+d*x]^k,x]*(b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{b,c,d,A,B,C},x] && OneQ[k^2] && k2===2*k  && RationalQ[n] && n<-1

Int[(A_+C_.*Sin[c_.+d_.*x_]^k2_)*(b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(21th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  2*A*Cos[c+d*x]*(b*Sin[c+d*x]^k)^(n+1)/(b*d*(2*n+k+1)) + 
  Dist[(2*A+(A+C)*(2*n+k+1))/(b^2*(2*n+k+1)),Int[(b*Sin[c+d*x]^k)^(n+2),x]]) /;
FreeQ[{b,c,d,A,C},x] && OneQ[k^2] && k2===2*k  && RationalQ[n] && n<-1

Int[(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*(b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(22th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -2*C*Cos[c+d*x]*(b*Sin[c+d*x]^k)^(n+1)/(b*d*(2*n+k+3)) + 
  Dist[1/(2*n+k+3),
    Int[Simplify[2*A+(A+C)*(2*n+k+1)+B*(2*n+k+3)*Sin[c+d*x]^k,x]*(b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{b,c,d,A,B,C},x] && OneQ[k^2] && k2===2*k && RationalQ[n] && n>-1

Int[(A_+C_.*Sin[c_.+d_.*x_]^k2_)*(b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(23th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -2*C*Cos[c+d*x]*(b*Sin[c+d*x]^k)^(n+1)/(b*d*(2*n+k+3)) + 
  Dist[(2*A+(A+C)*(2*n+k+1))/(2*n+k+3),Int[(b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{b,c,d,A,C},x] && OneQ[k^2] && k2===2*k && RationalQ[n] && n>-1

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)/(Sin[c_.+d_.*x_]*(a_+b_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(24th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A/a*Int[1/Sin[c+d*x],x] - 
  Dist[1/a,Int[(b*A-a*B-a*C*Sin[c+d*x])/(a+b*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]

Int[(A_+C_.*Sin[c_.+d_.*x_]^2)/(Sin[c_.+d_.*x_]*(a_+b_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(25th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A/a*Int[1/Sin[c+d*x],x] - 
  Dist[1/a,Int[(b*A-a*C*Sin[c+d*x])/(a+b*Sin[c+d*x]),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)/(Sqrt[Sin[c_.+d_.*x_]]*(a_+b_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(26th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[C/b,Int[Sqrt[Sin[c+d*x]],x]] + 
  Dist[1/b,Int[Simplify[b*A+(b*B-a*C)*Sin[c+d*x],x]/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]

Int[(A_+C_.*Sin[c_.+d_.*x_]^2)/(Sqrt[Sin[c_.+d_.*x_]]*(a_+b_.*Sin[c_.+d_.*x_])),x_Symbol] :=
(Print["Int(27th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[C/b,Int[Sqrt[Sin[c+d*x]],x]] + 
  Dist[1/b,Int[(b*A-a*C*Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)/(Sin[c_.+d_.*x_]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(28th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[C/b,Int[Sqrt[a+b*Sin[c+d*x]],x]] +
  Dist[1/b,Int[Simplify[b*A+(b*B-a*C)*Sin[c+d*x],x]/(Sin[c+d*x]*Sqrt[a+b*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]

Int[(A_+C_.*Sin[c_.+d_.*x_]^2)/(Sin[c_.+d_.*x_]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(29th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[C/b,Int[Sqrt[a+b*Sin[c+d*x]],x]] + 
  Dist[1/b,Int[(A*b-a*C*Sin[c+d*x])/(Sin[c+d*x]*Sqrt[a+b*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]

Int[(A_+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)/(Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(30th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  C*Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]*Tan[(c-Pi/2+d*x)/2]/(b*d) + 
  C/b*Int[Sqrt[a+b*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*(1+Sin[c+d*x])),x]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && ZeroQ[A-B] && ZeroQ[2*b*A-a*C]

Int[(A_+C_.*Sin[c_.+d_.*x_]^2)/(Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(31th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x] + 
  Dist[C,Int[Sin[c+d*x]^(3/2)/Sqrt[a+b*Sin[c+d*x]],x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)/(Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(32th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[1/(2*b),Int[(2*b*A-a*C+(2*b*B-a*C)*Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]] + 
  Dist[C/(2*b),Int[(a+a*Sin[c+d*x]+2*b*Sin[c+d*x]^2)/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)/(Sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(33th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[C,Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]] + 
  Int[(A+(B-C)*Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]

Int[(A_+C_.*Sin[c_.+d_.*x_]^2)/(Sin[c_.+d_.*x_]^(3/2)*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(34th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[C,Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]] + 
  Int[(A-C*Sin[c+d*x])/(Sin[c+d*x]^(3/2)*Sqrt[a+b*Sin[c+d*x]]),x]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)/(Sqrt[Sin[c_.+d_.*x_]]*(a_+b_.*Sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
(Print["Int(35th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[C/b,Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]] + 
  Dist[1/b,Int[(b*A-a*C+(b*B-C*(a+b))*Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]

Int[(A_+C_.*Sin[c_.+d_.*x_]^2)/(Sqrt[Sin[c_.+d_.*x_]]*(a_+b_.*Sin[c_.+d_.*x_])^(3/2)),x_Symbol] :=
(Print["Int(36th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[C/b,Int[(1+Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]] + 
  Dist[1/b,Int[(b*A-a*C-C*(a+b)*Sin[c+d*x])/(Sqrt[Sin[c+d*x]]*(a+b*Sin[c+d*x])^(3/2)),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]

Int[Sin[c_.+d_.*x_]^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(37th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[1/b^(k*m),Int[(A+B*Sin[c+d*x]^k+C*Sin[c+d*x]^(2*k))*(b*Sin[c+d*x]^k)^(k*m+n),x]]) /;
FreeQ[{b,c,d,A,B,C,n},x] && OneQ[k^2] && k2===2*k && IntegerQ[m]

Int[Sin[c_.+d_.*x_]^m_.*(A_+C_.*Sin[c_.+d_.*x_]^k2_)*(b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(38th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[1/b^(k*m),Int[(A+C*Sin[c+d*x]^(2*k))*(b*Sin[c+d*x]^k)^(k*m+n),x]]) /;
FreeQ[{b,c,d,A,C,n},x] && OneQ[k^2] && k2===2*k && IntegerQ[m]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (b_*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(39th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[b^(n-1/2)*Sqrt[b*Sin[c+d*x]^k]/(Sqrt[Sin[c+d*x]^j])^(j*k),
    Int[Sin[c+d*x]^(j*m+k*n)*(A+B*Sin[c+d*x]^k+C*Sin[c+d*x]^(2*k)),x]]) /;
FreeQ[{b,c,d,A,B,C},x] && OneQ[j^2,k^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && n>0

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(b_*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(40th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[b^(n-1/2)*Sqrt[b*Sin[c+d*x]^k]/(Sqrt[Sin[c+d*x]^j])^(j*k),
    Int[Sin[c+d*x]^(j*m+k*n)*(A+C*Sin[c+d*x]^(2*k)),x]]) /;
FreeQ[{b,c,d,A,C},x] && OneQ[j^2,k^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && n>0

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (b_*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(41th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[b^(n+1/2)*(Sqrt[Sin[c+d*x]^j])^(j*k)/Sqrt[b*Sin[c+d*x]^k],
    Int[Sin[c+d*x]^(j*m+k*n)*(A+B*Sin[c+d*x]^k+C*Sin[c+d*x]^(2*k)),x]]) /;
FreeQ[{b,c,d,A,B,C},x] && OneQ[j^2,k^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(b_*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(42th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[b^(n+1/2)*(Sqrt[Sin[c+d*x]^j])^(j*k)/Sqrt[b*Sin[c+d*x]^k],
    Int[Sin[c+d*x]^(j*m+k*n)*(A+C*Sin[c+d*x]^(2*k)),x]]) /;
FreeQ[{b,c,d,A,C},x] && OneQ[j^2,k^2] && IntegerQ[m-1/2] && IntegerQ[n-1/2] && n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))/
    (a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(43th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Int[(Sin[c+d*x]^j)^(m-j)*(C+B*Sin[c+d*x]+A*Sin[c+d*x]^2)/(b+a*Sin[c+d*x]),x]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2] && NonzeroQ[a^2-b^2] && RationalQ[m] && -1<m<=1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^(-2))/(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(44th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Int[(Sin[c+d*x]^j)^(m-j)*(C+A*Sin[c+d*x]^2)/(b+a*Sin[c+d*x]),x]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2] && NonzeroQ[a^2-b^2] && RationalQ[m] && -1<m<=1

Int[Sin[c_.+d_.*x_]*(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))/
    Sqrt[a_.+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(45th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]]),
    Int[(C+B*Sin[c+d*x]+A*Sin[c+d*x]^2)/(Sqrt[Sin[c+d*x]]*Sqrt[b+a*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2]

Int[Sin[c_.+d_.*x_]*(A_.+C_.*Sin[c_.+d_.*x_]^(-2))/Sqrt[a_.+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(46th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Csc[c+d*x]]),
    Int[(C+A*Sin[c+d*x]^2)/(Sqrt[Sin[c+d*x]]*Sqrt[b+a*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))/
    Sqrt[a_.+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(47th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/((Sqrt[Sin[c+d*x]^j])^j*Sqrt[a+b*Csc[c+d*x]]),
    Int[Sin[c+d*x]^(j*m-3/2)*(C+B*Sin[c+d*x]+A*Sin[c+d*x]^2)/Sqrt[b+a*Sin[c+d*x]],x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2] && NonzeroQ[a^2-b^2] && ZeroQ[j*m-1/2]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+C_.*Sin[c_.+d_.*x_]^(-2))/Sqrt[a_.+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(48th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sqrt[b+a*Sin[c+d*x]]/((Sqrt[Sin[c+d*x]^j])^j*Sqrt[a+b*Csc[c+d*x]]),
    Int[Sin[c+d*x]^(j*m-3/2)*(C+A*Sin[c+d*x]^2)/Sqrt[b+a*Sin[c+d*x]],x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2] && NonzeroQ[a^2-b^2] && ZeroQ[j*m-1/2]

Int[(Sin[c_.+d_.*x_]^(-1))^m_*(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)*
    (a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(49th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sqrt[Csc[c+d*x]]*Sqrt[Sin[c+d*x]],
    Int[(A+B*Sin[c+d*x]+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^m,x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && IntegerQ[m-1/2] && RationalQ[n] && 0<m<2 && -2<n<0

Int[(Sin[c_.+d_.*x_]^(-1))^m_*(A_.+C_.*Sin[c_.+d_.*x_]^2)*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(50th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[Sqrt[Csc[c+d*x]]*Sqrt[Sin[c+d*x]],
    Int[(A+C*Sin[c+d*x]^2)*(a+b*Sin[c+d*x])^n/Sin[c+d*x]^m,x]]) /;
FreeQ[{a,b,c,d,A,C},x] && IntegerQ[m-1/2] && RationalQ[n] && 0<m<2 && -2<n<0

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(51th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -(a^2*C-a*b*B+b^2*A)*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[Simplify[b*(a*A-b*B+a*C)*(n+1)-(a^2*C-a*b*B+b^2*A+(b^2*A-a*b*B+b^2*C)*(n+1))*Sin[c+d*x],x]*
      (a+b*Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && NonzeroQ[a^2*C-a*b*B+b^2*A] && RationalQ[n] && n<-1

Int[(A_.+C_.*Sin[c_.+d_.*x_]^2)*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(52th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -(a^2*C+b^2*A)*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[Simplify[a*b*(A+C)*(n+1)-(a^2*C+b^2*A+(b^2*A+b^2*C)*(n+1))*Sin[c+d*x],x]*
      (a+b*Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && NonzeroQ[a^2*C+b^2*A] && RationalQ[n] && n<-1

Int[Sin[c_.+d_.*x_]^(-1)*(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))*
    (a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(53th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -(a^2*C-a*b*B+b^2*A)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[Sin[c+d*x]^(-1)*
      Simplify[b*(a*A-b*B+a*C)*(n+1)-(a^2*C-a*b*B+b^2*A+(b^2*A-a*b*B+b^2*C)*(n+1))*Sin[c+d*x]^(-1),x]*
      (a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && NonzeroQ[a^2-b^2] && NonzeroQ[a^2*C-a*b*B+b^2*A] && RationalQ[n] && n<-1

Int[Sin[c_.+d_.*x_]^(-1)*(A_.+C_.*Sin[c_.+d_.*x_]^(-2))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(54th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -(a^2*C+b^2*A)*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[Sin[c+d*x]^(-1)*
      Simplify[a*b*(A+C)*(n+1)-(a^2*C+b^2*A+(b^2*A+b^2*C)*(n+1))*Sin[c+d*x]^(-1),x]*
      (a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && NonzeroQ[a^2-b^2] && NonzeroQ[a^2*C+b^2*A] && RationalQ[n] && n<-1

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)*(a_.+b_.*Sin[c_.+d_.*x_])^n_.,x_Symbol] :=
(Print["Int(55th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+2)) + 
  Dist[1/(b*(n+2)),
    Int[Simplify[b*A*(n+2)+b*C*(n+1)+(b*B*(n+2)-a*C)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && RationalQ[n] && n>-1

Int[(A_.+C_.*Sin[c_.+d_.*x_]^2)*(a_.+b_.*Sin[c_.+d_.*x_])^n_.,x_Symbol] :=
(Print["Int(56th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n+1)/(b*d*(n+2)) + 
  Dist[1/(b*(n+2)),
    Int[Simplify[b*A*(n+2)+b*C*(n+1)-a*C*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^n,x]]) /;
FreeQ[{a,b,c,d,A,C},x] && RationalQ[n] && n>-1

Int[Sin[c_.+d_.*x_]^(-1)*(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))*
    (a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_.,x_Symbol] :=
(Print["Int(57th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+2)) + 
  Dist[1/(b*(n+2)),
    Int[Sin[c+d*x]^(-1)*
      Simplify[b*A*(n+2)+b*C*(n+1)+(b*B*(n+2)-a*C)*Sin[c+d*x]^(-1),x]*(a+b*Sin[c+d*x]^(-1))^n,x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && RationalQ[n] && n>-1

Int[Sin[c_.+d_.*x_]^(-1)*(A_.+C_.*Sin[c_.+d_.*x_]^(-2))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_.,x_Symbol] :=
(Print["Int(58th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n+1)/(b*d*(n+2)) + 
  Dist[1/(b*(n+2)),
    Int[Sin[c+d*x]^(-1)*
      Simplify[b*A*(n+2)+b*C*(n+1)-a*C*Sin[c+d*x]^(-1),x]*(a+b*Sin[c+d*x]^(-1))^n,x]]) /;
FreeQ[{a,b,c,d,A,C},x] && RationalQ[n] && n>-1

(* Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(59th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  a*A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[(j*k*m+(k+1)/2)*(b*A+a*B)+((j*k*m+(k+3)/2)*a*A+(j*k*m+(k+1)/2)*(b*B+a*C))*Sin[c+d*x]^k+
        (j*k*m+(k+1)/2)*b*C*Sin[c+d*x]^(2*k),x],x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && RationalQ[m] && j*k*m<-1 *)

(* Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(60th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  a*A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[(j*k*m+(k+1)/2)*b*A+((j*k*m+(k+3)/2)*a*A+(j*k*m+(k+1)/2)*a*C)*Sin[c+d*x]^k+
        (j*k*m+(k+1)/2)*b*C*Sin[c+d*x]^(2*k),x],x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && RationalQ[m] && j*k*m<-1 *)

(* Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(61th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -b*C*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+2*j*k)/(d*(j*k*m+(k+5)/2)) + 
  Dist[1/(j*k*m+(k+5)/2),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[(j*k*m+(k+5)/2)*a*A+((j*k*m+(k+5)/2)*(b*A+a*B)+(j*k*m+(k+3)/2)*b*C)*Sin[c+d*x]^k+
        (j*k*m+(k+5)/2)*(b*B+a*C)*Sin[c+d*x]^(2*k),x],x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && RationalQ[m] && j*k*m>=-1 *)

(* Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.),x_Symbol] :=
(Print["Int(62th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -b*C*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+2*j*k)/(d*(j*k*m+(k+5)/2)) + 
  Dist[1/(j*k*m+(k+5)/2),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[(j*k*m+(k+5)/2)*a*A+((j*k*m+(k+5)/2)*b*A+(j*k*m+(k+3)/2)*b*C)*Sin[c+d*x]^k+
        (j*k*m+(k+5)/2)*a*C*Sin[c+d*x]^(2*k),x],x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && RationalQ[m] && j*k*m>=-1 *)

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(63th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[1/b^2,Int[(Sin[c+d*x]^j)^m*Simplify[b*B-a*C+b*C*Sin[c+d*x]^k,x]*(a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C,m},x] && OneQ[j^2,k^2] && k2===2*k && ZeroQ[a^2*C-a*b*B+b^2*A] && RationalQ[n] && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(64th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  Dist[1/b^2,Int[(Sin[c+d*x]^j)^m*Simplify[-a*C+b*C*Sin[c+d*x]^k,x]*(a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C,m},x] && OneQ[j^2,k^2] && k2===2*k && ZeroQ[a^2*C+b^2*A] && RationalQ[n] && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(65th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -(a^2*C-a*b*B+b^2*A)*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[(a^2*C-a*b*B+b^2*A)*(j*k*m+(k-1)/2)+b*(a*A-b*B+a*C)*(n+1)*Sin[c+d*x]^k-
        ((b^2*A-a*b*B+b^2*C)*(n+1)+(a^2*C-a*b*B+b^2*A)*(j*k*m+(k+1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  NonzeroQ[a^2*C-a*b*B+b^2*A] && RationalQ[m,n] && j*k*m>0 && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(66th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -(a^2*C+b^2*A)*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(b*(n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[(a^2*C+b^2*A)*(j*k*m+(k-1)/2)+b*(a*A+a*C)*(n+1)*Sin[c+d*x]^k-
        ((b^2*A+b^2*C)*(n+1)+(a^2*C+b^2*A)*(j*k*m+(k+1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  NonzeroQ[a^2*C+b^2*A] && RationalQ[m,n] && j*k*m>0 && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(67th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(j*k*m+n+(k+3)/2)) + 
  Dist[1/(b*(j*k*m+n+(k+3)/2)),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[a*C*(j*k*m+(k-1)/2)+b*(A+(A+C)*(j*k*m+n+(k+1)/2))*Sin[c+d*x]^k+
        (b*B*(n+1)+(b*B-a*C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m>0 && -1<=n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(68th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n+1)/(b*d*(j*k*m+n+(k+1)/2+1)) + 
  Dist[1/(b*(j*k*m+n+(k+1)/2+1)),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[a*C*(j*k*m+(k-1)/2)+b*(A+(A+C)*(j*k*m+n+(k+1)/2))*Sin[c+d*x]^k-
        a*C*(j*k*m+(k+1)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m>0 && -1<=n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(69th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+3)/2+n)) + 
  Dist[1/(j*k*m+(k+3)/2+n),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*(A*(n+1)+(A+C)*(j*k*m+(k+1)/2))+(b*A+a*B+(b*A+a*B+b*C)*(j*k*m+(k+1)/2+n))*Sin[c+d*x]^k+
        (a*C*n+b*B*(j*k*m+(k+3)/2+n))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m>=-1 && Not[m^2==1 && k==-1] && n>0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(70th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  -C*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+3)/2+n)) + 
  Dist[1/(j*k*m+(k+3)/2+n),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*(A*(n+1)+(A+C)*(j*k*m+(k+1)/2))+(b*A+(b*A+b*C)*(j*k*m+(k+1)/2+n))*Sin[c+d*x]^k+
        a*C*n*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m>=-1 && Not[m^2==1 && k==-1] && n>0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(71th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[a*B*(j*k*m+(k+1)/2)-b*A*n+(a*A+(a*A+a*C+b*B)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k+
        b*(A*(n+1)+(A+C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m+(k+1)/2!=0 && j*k*m<=-1 && n>0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(72th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[-b*A*n+a*(A+(A+C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k+
        b*(A*(n+1)+(A+C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m+(k+1)/2!=0 && j*k*m<=-1 && n>0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(73th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(a*d*(j*k*m+(k+1)/2)) + 
  Dist[1/(a*(j*k*m+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[(a*B-b*A)*(j*k*m+(k+1)/2)-b*A*(n+1)+a*(A+(A+C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k+
        b*A*(j*k*m+n+(k+5)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m+(k+1)/2!=0 && j*k*m<=-1 && -1<=n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(74th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(a*d*(j*k*m+(k+1)/2)) + 
  Dist[1/(a*(j*k*m+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[-b*A*(j*k*m+(k+1)/2)-b*A*(n+1)+a*(A+(A+C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k+
        b*A*(j*k*m+n+(k+5)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m+(k+1)/2!=0 && j*k*m<=-1 && -1<=n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(75th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  (a^2*C-a*b*B+b^2*A)*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(a*(n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[A*(a^2-b^2)*(n+1)-(a^2*C-a*b*B+b^2*A)*(j*k*m+(k+1)/2)-a*(b*A-a*B+b*C)*(n+1)*Sin[c+d*x]^k+
        (a^2*C-a*b*B+b^2*A)*(j*k*m+n+(k+5)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  NonzeroQ[a^2*C-a*b*B+b^2*A] && RationalQ[m,n] && j*k*m<0 && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(76th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+b sin^k)^n.m"];
  (a^2*C+b^2*A)*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n+1)/(a*d*(n+1)*(a^2-b^2)) + 
  Dist[1/(a*(n+1)*(a^2-b^2)),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[A*(a^2-b^2)*(n+1)-(a^2*C+b^2*A)*(j*k*m+(k+1)/2)-a*b*(A+C)*(n+1)*Sin[c+d*x]^k+
        (a^2*C+b^2*A)*(j*k*m+n+(k+5)/2)*Sin[c+d*x]^(2*k),x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && NonzeroQ[a^2-b^2] && 
  NonzeroQ[a^2*C+b^2*A] && RationalQ[m,n] && j*k*m<0 && n<-1
