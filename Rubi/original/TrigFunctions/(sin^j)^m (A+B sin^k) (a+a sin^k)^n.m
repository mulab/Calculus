(* ::Package:: *)

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1))/(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(1th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  A*x/a - Dist[(b*A-a*B)/a,Int[Sin[c+d*x]^(-1)/(a+b*Sin[c+d*x]^(-1)),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B]

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(2th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -(b*A-a*B)*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) + 
  Dist[1/(b^2*(2*n+1)),
    Int[Simplify[a*A*(2*n+1)-((b*A-a*B)*(n+1))*Sin[c+d*x]^(-1),x]*(a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && n<-1

Int[(A_+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(3th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -b*B*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-1)/(d*n) + 
  Dist[1/n,
    Int[Simplify[a*A*n+(a*B*(2*n-1)+b*A*n)*Sin[c+d*x]^(-1),x]*(a+b*Sin[c+d*x]^(-1))^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && n>0

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sin[c_.+d_.*x_]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(4th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  Dist[A/a,Int[Sqrt[a+b*Sin[c+d*x]]/Sin[c+d*x],x]] - 
  Dist[(a*A-b*B)/b,Int[1/Sqrt[a+b*Sin[c+d*x]],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B]

Int[(A_+B_.*Sin[c_.+d_.*x_]^(-1))/Sqrt[a_+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(5th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  A/a*Int[Sqrt[a+b*Sin[c+d*x]^(-1)],x] - 
  (b*A-a*B)/a*Int[Sin[c+d*x]^(-1)/Sqrt[a+b*Sin[c+d*x]^(-1)],x]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B]

Int[(A_+B_.*Sin[c_.+d_.*x_])/(Sqrt[Sin[c_.+d_.*x_]]*Sqrt[a_+b_.*Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(6th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  Dist[B/b,Int[Sqrt[a+b*Sin[c+d*x]]/Sqrt[Sin[c+d*x]],x]] + 
  Dist[(b*A-a*B)/b,Int[1/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+B_.*Sin[c_.+d_.*x_]^(-1))*Sqrt[a_+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(7th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -2*a*A*Cos[c+d*x]/(d*(Sin[c+d*x]^j)^m*Sqrt[a+b*Csc[c+d*x]]) + 
  Dist[B,Int[Sqrt[a+b*Sin[c+d*x]^(-1)]/(Sin[c+d*x]^j)^m,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2] && ZeroQ[a^2-b^2] && RationalQ[m] && j*m==1/2

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^(-1))/Sqrt[a_+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(8th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  Dist[B/b,Int[(Sin[c+d*x]^j)^m*Sqrt[a+b*Sin[c+d*x]^(-1)],x]] + 
  Dist[(b*A-a*B)/b,Int[(Sin[c+d*x]^j)^m/Sqrt[a+b*Sin[c+d*x]^(-1)],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2] && ZeroQ[a^2-b^2] && RationalQ[m] && j*m==-1/2 && 
  NonzeroQ[b*A-a*B]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+B_.*Sin[c_.+d_.*x_]^(-1))/Sqrt[a_+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(9th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -2*A*Cos[c+d*x]/(d*(Sin[c+d*x]^j)^m*Sqrt[a+b*Csc[c+d*x]]) - 
  Dist[(b*A-a*B)/a,Int[1/((Sin[c+d*x]^j)^m*Sqrt[a+b*Sin[c+d*x]^(-1)]),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2] && ZeroQ[a^2-b^2] && RationalQ[m] && j*m==1/2 && 
  NonzeroQ[b*A-a*B]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*Sqrt[a_+b_.*Sin[c_.+d_.*x_]^k_.],x_Symbol] :=
(Print["Int(10th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  a*A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+1)/2)*Sqrt[a+b*Sin[c+d*x]^k])) /;
FreeQ[{a,b,c,d,A,B,m},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  NonzeroQ[j*k*m+(k+1)/2] && ZeroQ[a*B*(j*k*m+(k+1)/2)+b*A*(j*k*m+(k+2)/2)]

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*Sqrt[a_+b_.*Sin[c_.+d_.*x_]^k_.],x_Symbol] :=
(Print["Int(11th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  a*A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+1)/2)*Sqrt[a+b*Sin[c+d*x]^k]) + 
  Dist[(a*B*(j*k*m+(k+1)/2)+b*A*(j*k*m+(k+2)/2))/(a*(j*k*m+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m+j*k)*Sqrt[a+b*Sin[c+d*x]^k],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m] && NonzeroQ[j*k*m+(k+1)/2] && j*k*m<=-1 && 
  NonzeroQ[a*B*(j*k*m+(k+1)/2)+b*A*(j*k*m+(k+2)/2)]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*Sqrt[a_+b_.*Sin[c_.+d_.*x_]^k_.],x_Symbol] :=
(Print["Int(12th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -b*B*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(j*k*m+(k+2)/2)*Sqrt[a+b*Sin[c+d*x]^k]) + 
  Dist[(a*B*(j*k*m+(k+1)/2)+b*A*(j*k*m+(k+2)/2))/(b*(j*k*m+(k+2)/2)),
    Int[(Sin[c+d*x]^j)^m*Sqrt[a+b*Sin[c+d*x]^k],x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m] && NonzeroQ[j*k*m+(k+2)/2] && j*k*m>=-1 && 
  NonzeroQ[a*B*(j*k*m+(k+1)/2)+b*A*(j*k*m+(k+2)/2)]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(13th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(n+1))) /;
FreeQ[{a,b,c,d,A,B,m,n},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  ZeroQ[j*k*m+n+(k+3)/2] && NonzeroQ[n+1] && ZeroQ[a*B*(n+1)+b*A*n]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(14th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(n+1)) + 
  Dist[(a*B*(n+1)+b*A*n)/(a*(n+1)),Int[(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && ZeroQ[j*k*m+n+(k+3)/2] && n>-1 && NonzeroQ[a*B*(n+1)+b*A*n]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(15th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -(b*A-a*B)*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(b*d*(2*n+1))) /;
FreeQ[{a,b,c,d,A,B,m,n},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  ZeroQ[j*k*m+n+(k+3)/2] && NonzeroQ[2*n+1] && ZeroQ[b*B*(n+1)+a*A*n]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(16th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -(b*A-a*B)*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(b*d*(2*n+1)) + 
  Dist[(b*B*(n+1)+a*A*n)/(a^2*(2*n+1)),Int[(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && ZeroQ[j*k*m+n+(k+3)/2] && n<=-1 && NonzeroQ[b*B*(n+1)+a*A*n]

Int[(A_.+B_.*Sin[c_.+d_.*x_])*(a_+b_.*Sin[c_.+d_.*x_])^n_.,x_Symbol] :=
(Print["Int(17th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -B*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(n+1))) /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[a^2-b^2] && ZeroQ[a*B*n+b*A*(n+1)]

Int[Sin[c_.+d_.*x_]^(-1)*(A_+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_.,x_Symbol] :=
(Print["Int(18th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -B*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1))) /;
FreeQ[{a,b,c,d,A,B,n},x] && ZeroQ[a^2-b^2] && ZeroQ[a*B*n+b*A*(n+1)]

Int[(A_.+B_.*Sin[c_.+d_.*x_])*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(19th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  (b*A-a*B)*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) + 
  Dist[(a*B*n+b*A*(n+1))/(a*b*(2*n+1)),Int[(a+b*Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && n<=-1 && 
  NonzeroQ[a*B*n+b*A*(n+1)]

Int[Sin[c_.+d_.*x_]^(-1)*(A_+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(20th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  (b*A-a*B)*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(a*d*(2*n+1)) + 
  Dist[(a*B*n+b*A*(n+1))/(a*b*(2*n+1)),Int[Sin[c+d*x]^(-1)*(a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && n<=-1 && 
  NonzeroQ[a*B*n+b*A*(n+1)]

Int[(A_.+B_.*Sin[c_.+d_.*x_])*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(21th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -B*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(d*(n+1)) + 
  Dist[(a*B*n+b*A*(n+1))/(b*(n+1)),Int[(a+b*Sin[c+d*x])^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && 
  n>-1 && n!=1 && NonzeroQ[a*B*n+b*A*(n+1)]

Int[Sin[c_.+d_.*x_]^(-1)*(A_+B_.*Sin[c_.+d_.*x_]^(-1))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(22th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -B*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  Dist[(a*B*n+b*A*(n+1))/(b*(n+1)),Int[Sin[c+d*x]^(-1)*(a+b*Sin[c+d*x]^(-1))^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && RationalQ[n] && 
  n>-1 && n!=1 && NonzeroQ[a*B*n+b*A*(n+1)]

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(23th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  (b*A-a*B)*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^n/(a*d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[-(b*A-a*B)*(j*k*m+(k-1)/2)+(b*B*n+a*A*(n+1)+(a*A-b*B)*(j*k*m+(k-1)/2))*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && j*k*m>0 && n<=-1 && Not[j*k*m==1 && n==-1]

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(24th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -B*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+n+(k+1)/2)) + 
  Dist[1/(a*(j*k*m+n+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m-j*k)*
      Simplify[a*B*(j*k*m+(k-1)/2)+(b*B*n+a*A*(j*k*m+n+(k+1)/2))*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && NonzeroQ[j*k*m+n+(k+1)/2] && j*k*m>0 && -1<n<0 && Not[j*m==1 && k==1]

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(25th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -b*B*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-1)/(d*(j*k*m+n+(k+1)/2)) + 
  Dist[1/(j*k*m+n+(k+1)/2),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*A*n+(a*A+b*B)*(j*k*m+(k+1)/2)+(b*A+a*B*n+(b*A+a*B)*(j*k*m+n+(k-1)/2))*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && NonzeroQ[j*k*m+n+(k+1)/2] && j*k*m>=-1 && n>0 && n!=1/2 && Not[j*m==1 && k==1]

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(26th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  a*A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-1)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[(b*A+a*B)*(j*k*m+(k+1)/2)-b*A*(n-1)+(a*A*n+(a*A+b*B)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && j*k*m<-1 && n>0 && n!=1/2

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(27th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(a*(j*k*m+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[a*B*(j*k*m+(k+1)/2)-b*A*n+a*A*(j*k*m+n+(k+3)/2)*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && NonzeroQ[j*k*m+(k+1)/2] && j*k*m<=-1 && -1<n<0

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+B_.*Sin[c_.+d_.*x_]^k_.)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(28th)@(sin^j)^m (A+B sin^k) (a+a sin^k)^n.m"];
  -(b*A-a*B)*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(b*d*(2*n+1)) + 
  Dist[1/(b^2*(2*n+1)),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*A*(2*n+1)+(a*A-b*B)*(j*k*m+(k+1)/2)-(b*A-a*B)*(j*k*m+n+(k+3)/2)*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && NonzeroQ[b*A-a*B] && 
  RationalQ[m,n] && j*k*m<0 && n<=-1
