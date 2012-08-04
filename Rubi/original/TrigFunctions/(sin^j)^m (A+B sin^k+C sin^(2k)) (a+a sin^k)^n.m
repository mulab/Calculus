(* ::Package:: *)

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))/(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(1th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  A*x/a + 
  C/b*Int[Sin[c+d*x]^(-1),x] - 
  (b*A-a*B+b*C)/a*Int[Sin[c+d*x]^(-1)/(a+b*Sin[c+d*x]^(-1)),x]) /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2]

Int[(A_.+C_.*Sin[c_.+d_.*x_]^(-2))/(a_+b_.*Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(2th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  A*x/a + C/b*Int[Sin[c+d*x]^(-1),x] - 
  (b*A+b*C)/a*Int[Sin[c+d*x]^(-1)/(a+b*Sin[c+d*x]^(-1)),x]) /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2]

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))/Sqrt[a_.+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(3th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  -2*C*Cot[c+d*x]/(d*Sqrt[a+b*Csc[c + d*x]]) + 
  Dist[1/a,Int[Simplify[a*A+(a*B-b*C)*Sin[c+d*x]^(-1),x]/Sqrt[a+b*Sin[c+d*x]^(-1)],x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2]

Int[(A_+C_.*Sin[c_.+d_.*x_]^(-2))/Sqrt[a_.+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(4th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  -2*C*Cot[c+d*x]/(d*Sqrt[a+b*Csc[c + d*x]]) + 
  Dist[1/a,Int[Simplify[a*A-b*C*Sin[c+d*x]^(-1),x]/Sqrt[a+b*Sin[c+d*x]^(-1)],x]]) /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2]

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))/
    Sqrt[a_.+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(5th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  -2*A*Cos[c+d*x]/(d*(Sin[c+d*x]^j)^m*Sqrt[a+b*Csc[c+d*x]]) - 
  Dist[1/a,
    Int[Simplify[b*A-a*B-a*C*Sin[c+d*x]^(-1),x]/((Sin[c+d*x]^j)^m*Sqrt[a+b*Sin[c+d*x]^(-1)]),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2] && ZeroQ[a^2-b^2] && RationalQ[m] && j*m==1/2

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+C_.*Sin[c_.+d_.*x_]^(-2))/Sqrt[a_.+b_.*Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(6th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  -2*A*Cos[c+d*x]/(d*(Sin[c+d*x]^j)^m*Sqrt[a+b*Csc[c+d*x]]) - 
  Dist[1/a,
    Int[Simplify[b*A-a*C*Sin[c+d*x]^(-1),x]/((Sin[c+d*x]^j)^m*Sqrt[a+b*Sin[c+d*x]^(-1)]),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2] && ZeroQ[a^2-b^2] && RationalQ[m] && j*m==1/2

Int[(A_.+B_.*Sin[c_.+d_.*x_]+C_.*Sin[c_.+d_.*x_]^2)*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(7th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  (b*(A+C)-a*B)*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),
    Int[Simplify[a*A*(n+1)+n*(b*B-a*C)+b*C*(2*n+1)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[(A_.+C_.*Sin[c_.+d_.*x_]^2)*(a_+b_.*Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(8th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  b*(A+C)*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),
    Int[Simplify[a*A*(n+1)-a*C*n+b*C*(2*n+1)*Sin[c+d*x],x]*(a+b*Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[(A_.+B_.*Sin[c_.+d_.*x_]^(-1)+C_.*Sin[c_.+d_.*x_]^(-2))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(9th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  (a*B-b*(A+C))*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(b*d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),
    Int[Simplify[a*A*(2*n+1)+(b*C*n-(b*A-a*B)*(n+1))*Sin[c+d*x]^(-1),x]*(a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[(A_.+C_.*Sin[c_.+d_.*x_]^(-2))*(a_+b_.*Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(10th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  -(A+C)*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),
    Int[Simplify[a*A*(2*n+1)+(b*C*n-b*A*(n+1))*Sin[c+d*x]^(-1),x]*(a+b*Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(11th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  Int[(Sin[c+d*x]^j)^(m+j*k)*(B+C*Sin[c+d*x]^k)*(a+b*Sin[c+d*x]^k)^n,x]) /;
FreeQ[{a,b,c,d,B,C,m,n},x] && OneQ[j^2,k^2] && k2===2*k && ZeroQ[a^2-b^2]

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(12th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  (a*B-b*A-b*C)*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(b*d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*A*(2*n+1)-(b*B-a*A-a*C)*(j*k*m+(k+1)/2)+
        (b*C*n-(b*A-a*B)*(n+1)+(a*B-b*A-b*C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && ZeroQ[a^2-b^2] && 
  RationalQ[m,n] && n<=-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(13th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  -(A+C)*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*A*(2*n+1)+a*(A+C)*(j*k*m+(k+1)/2)+
        (b*C*n-b*A*(n+1)-b*(A+C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && ZeroQ[a^2-b^2] && 
  RationalQ[m,n] && n<=-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(14th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(a*(j*k*m+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[a*B*(j*k*m+(k+1)/2)-b*A*n+a*(A*(n+1)+(A+C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && ZeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m<-1 && n>-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(15th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  A*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(a*(j*k*m+(k+1)/2)),
    Int[(Sin[c+d*x]^j)^(m+j*k)*
      Simplify[-b*A*n+a*(A*(n+1)+(A+C)*(j*k*m+(k+1)/2))*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && ZeroQ[a^2-b^2] && 
  RationalQ[m,n] && j*k*m<-1 && n>-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_+B_.*Sin[c_.+d_.*x_]^k_.+C_.*Sin[c_.+d_.*x_]^k2_)*
    (a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(16th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  -C*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+n+(k+3)/2)) + 
  Dist[1/(a*(j*k*m+n+(k+3)/2)),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*A*(n+1)+a*(A+C)*(j*k*m+(k+1)/2)+(b*C*n+a*B*(j*k*m+n+(k+3)/2))*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,B,C},x] && OneQ[j^2,k^2] && k2===2*k && ZeroQ[a^2-b^2] && 
  RationalQ[m,n] && NonzeroQ[j*k*m+n+(k+3)/2] && j*k*m>=-1 && n>-1

Int[(Sin[c_.+d_.*x_]^j_.)^m_.*(A_.+C_.*Sin[c_.+d_.*x_]^k2_)*(a_+b_.*Sin[c_.+d_.*x_]^k_.)^n_.,x_Symbol] :=
(Print["Int(17th)@(sin^j)^m (A+B sin^k+C sin^(2k)) (a+a sin^k)^n.m"];
  -C*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+n+(k+3)/2)) + 
  Dist[1/(a*(j*k*m+n+(k+3)/2)),
    Int[(Sin[c+d*x]^j)^m*
      Simplify[a*A*(n+1)+a*(A+C)*(j*k*m+(k+1)/2)+b*C*n*Sin[c+d*x]^k,x]*
      (a+b*Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d,A,C},x] && OneQ[j^2,k^2] && k2===2*k && ZeroQ[a^2-b^2] && 
  RationalQ[m,n] && NonzeroQ[j*k*m+n+(k+3)/2] && j*k*m>=-1 && n>-1
