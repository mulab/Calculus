(* ::Package:: *)

Int[1/(a_+b_.* Sin[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(1th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cos[c+d*x]/(d*(b+a*Sin[c+d*x]))) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[1/(a_+b_.*Cos[c_.+d_.*x_]),x_Symbol] :=
(Print["Int(2th)@(sin^j)^m (a+a sin^k)^n.m"];
  Sin[c+d*x]/(d*(b+a*Cos[c+d*x]))) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[1/(a_+b_.* Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(3th)@(sin^j)^m (a+a sin^k)^n.m"];
  x/a - Dist[b/a,Int[1/( Sin[c+d*x]*(a+b/ Sin[c+d*x])),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[Sqrt[a_+b_.* Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(4th)@(sin^j)^m (a+a sin^k)^n.m"];
  -2*b*Cos[c+d*x]/(d*Sqrt[a+b*Sin[c+d*x]])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[Sqrt[a_+b_.*Cos[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(5th)@(sin^j)^m (a+a sin^k)^n.m"];
  2*b*Sin[c+d*x]/(d*Sqrt[a+b*Cos[c+d*x]])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[Sqrt[a_+b_.* Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(6th)@(sin^j)^m (a+a sin^k)^n.m"];
  -2*Sqrt[a]/d*ArcTan[(Sqrt[a]*Cot[c+d*x])/Sqrt[a+b*Csc[c+d*x]]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[1/Sqrt[a_+b_.* Sin[c_.+Pi/2+d_.*x_]],x_Symbol] :=
(Print["Int(7th)@(sin^j)^m (a+a sin^k)^n.m"];
  2/(d*Sqrt[a+b*Cos[c+d*x]])*Cos[(c+d*x)/2]*ArcTanh[Sin[(c+d*x)/2]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b]

Int[1/Sqrt[a_+b_.* Sin[c_.+Pi/2+d_.*x_]],x_Symbol] :=
(Print["Int(8th)@(sin^j)^m (a+a sin^k)^n.m"];
  -2/(d*Sqrt[a+b*Cos[c+d*x]])*Sin[(c+d*x)/2]*ArcTanh[Cos[(c+d*x)/2]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b]

Int[1/Sqrt[a_+b_.* Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(9th)@(sin^j)^m (a+a sin^k)^n.m"];
  2/(d*Sqrt[a+b*Sin[c+d*x]])*Cos[(c+d*x)/2-Pi*b/(4*a)]*ArcTanh[Sin[(c+d*x)/2-Pi*b/(4*a)]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[(a_+b_.* Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(10th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),Int[(a*(2*n+1)-(b*(n+1))* Sin[c+d*x]^(-1))*(a+b* Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[(a_+b_.* Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(11th)@(sin^j)^m (a+a sin^k)^n.m"];
  -b^2*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-2)/(d*(n-1)) + 
  Dist[a/(n-1),Int[(a*(n-1)+(b*(3*n-4))* Sin[c+d*x]^(-1))*(a+b* Sin[c+d*x]^(-1))^(n-2),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>1 && n!=2

Int[Sqrt[a_+b_.* Sin[c_.+Pi/2+d_.*x_]]/ Sin[c_.+Pi/2+d_.*x_],x_Symbol] :=
(Print["Int(12th)@(sin^j)^m (a+a sin^k)^n.m"];
  2*Sqrt[2]*b*Cos[(c+d*x)/2]/(d*Sqrt[a+b*Cos[c+d*x]])*ArcTanh[Sqrt[2]*Sin[(c+d*x)/2]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b]

Int[Sqrt[a_+b_.* Sin[c_.+Pi/2+d_.*x_]]/ Sin[c_.+Pi/2+d_.*x_],x_Symbol] :=
(Print["Int(13th)@(sin^j)^m (a+a sin^k)^n.m"];
  2*Sqrt[2]*a*Sin[(c+d*x)/2]/(d*Sqrt[a+b*Cos[c+d*x]])*ArcTanh[Sqrt[2]*Cos[(c+d*x)/2]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a+b]

Int[Sqrt[a_+b_.* Sin[c_.+d_.*x_]]/ Sin[c_.+d_.*x_],x_Symbol] :=
(Print["Int(14th)@(sin^j)^m (a+a sin^k)^n.m"];
  2*Sqrt[2]*b*Cos[(c+d*x)/2-Pi*b/(4*a)]/(d*Sqrt[a+b*Sin[c+d*x]])*
    ArcTanh[Sqrt[2]*Sin[(c+d*x)/2-Pi*b/(4*a)]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[1/( Sin[c_.+d_.*x_]*Sqrt[a_+b_.* Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(15th)@(sin^j)^m (a+a sin^k)^n.m"];
  Dist[1/a,Int[Sqrt[a+b* Sin[c+d*x]]/ Sin[c+d*x],x]] - 
  Dist[b/a,Int[1/Sqrt[a+b* Sin[c+d*x]],x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[1/Sqrt[a_+b_.* Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(16th)@(sin^j)^m (a+a sin^k)^n.m"];
  1/a*Int[Sqrt[a+b* Sin[c+d*x]^(-1)],x] - 
  b/a*Int[ Sin[c+d*x]^(-1)/Sqrt[a+b* Sin[c+d*x]^(-1)],x]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[1/(Sqrt[ Sin[c_.+Pi/2+d_.*x_]]*Sqrt[a_+b_.* Sin[c_.+Pi/2+d_.*x_]]),x_Symbol] :=
(Print["Int(17th)@(sin^j)^m (a+a sin^k)^n.m"];
  Sqrt[2]/(d*Sqrt[a])*ArcSin[Tan[(c+d*x)/2]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PositiveQ[a]

Int[1/(Sqrt[ Sin[c_.+d_.*x_]]*Sqrt[a_+b_.* Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(18th)@(sin^j)^m (a+a sin^k)^n.m"];
  Sqrt[2]/(d*Sqrt[a])*ArcSin[Tan[(c+d*x)/2-Pi/4]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a-b] && PositiveQ[a]

Int[1/(Sqrt[ Sin[c_.+d_.*x_]]*Sqrt[a_+b_.* Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(19th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Sqrt[2]*Sqrt[b]/(a*d)*ArcTan[Sqrt[b]*Cos[c+d*x]/(Sqrt[2]*Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]])]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && Not[ZeroQ[a-b] && PositiveQ[a]]

Int[Sqrt[a_+b_.* Sin[c_.+d_.*x_]]/Sqrt[ Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(20th)@(sin^j)^m (a+a sin^k)^n.m"];
  -2*Sqrt[b]/d*ArcTan[Sqrt[b]*Cos[c+d*x]/(Sqrt[Sin[c+d*x]]*Sqrt[a+b*Sin[c+d*x]])]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[Sqrt[ Sin[c_.+d_.*x_]]/Sqrt[a_+b_.* Sin[c_.+d_.*x_]],x_Symbol] :=
(Print["Int(21th)@(sin^j)^m (a+a sin^k)^n.m"];
  Dist[1/b,Int[Sqrt[a+b* Sin[c+d*x]]/Sqrt[ Sin[c+d*x]],x]] - 
  Dist[a/b,Int[1/(Sqrt[ Sin[c+d*x]]*Sqrt[a+b* Sin[c+d*x]]),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[( Sin[c_.+d_.*x_]^j_.)^m_./(a_+b_.* Sin[c_.+d_.*x_]^k_.)^2,x_Symbol] :=
(Print["Int(22th)@(sin^j)^m (a+a sin^k)^n.m"];
  -a*Cos[c+d*x]*(Sin[c+d*x]^j)^m/(3*b*d*(a+b*Sin[c+d*x]^k)^2) + 
  1/(6*a*b)*Int[( Sin[c+d*x]^j)^(m-j*k),x]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m] && 
  ZeroQ[2*j*k*m+k-2]

(* Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(23th)@(sin^j)^m (a+a sin^k)^n.m"];
  a*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^n/(b*d*(2*n+1)) + 
  Dist[(n+1)/(2*a*b*(2*n+1)),Int[( Sin[c+d*x]^j)^(m-j*k)*(a+b* Sin[c+d*x]^k)^(n+2),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  ZeroQ[2*j*k*m+n+k] && j*k*m>0 && n<-1 *)

Int[ Sin[c_.+d_.*x_]^(-1)/(a_+b_.* Sin[c_.+d_.*x_]^(-1)),x_Symbol] :=
(Print["Int(24th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cot[c+d*x]/(d*(b+a*Csc[c+d*x]))) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[ Sin[c_.+d_.*x_]^(-1)*Sqrt[a_+b_.* Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(25th)@(sin^j)^m (a+a sin^k)^n.m"];
  -2*b*Cot[c+d*x]/(d*Sqrt[a+b*Csc[c+d*x]])) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[1/( Sin[c_.+d_.*x_]*Sqrt[a_+b_.* Sin[c_.+d_.*x_]^(-1)]),x_Symbol] :=
(Print["Int(26th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Sqrt[2*a]/(b*d)*ArcTan[Sqrt[a]*Cot[c + d*x]/(Sqrt[2]*Sqrt[a + b*Csc[c + d*x]])]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[ Sin[c_.+d_.*x_]^(-2)*(a_+b_.* Sin[c_.+d_.*x_]^(-1))^n_.,x_Symbol] :=
(Print["Int(27th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(2*n+1)) + 
  Dist[n/(b*(2*n+1)),Int[ Sin[c+d*x]^(-1)*(a+b* Sin[c+d*x]^(-1))^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[ Sin[c_.+d_.*x_]^(-2)*(a_+b_.* Sin[c_.+d_.*x_]^(-1))^n_.,x_Symbol] :=
(Print["Int(28th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(d*(n+1)) + 
  Dist[b*n/(a*(n+1)),Int[ Sin[c+d*x]^(-1)*(a+b* Sin[c+d*x]^(-1))^n,x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>-1 && n!=1 && n!=2

Int[( Sin[c_.+d_.*x_]^j_.)^m_/Sqrt[a_+b_.* Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(29th)@(sin^j)^m (a+a sin^k)^n.m"];
  Dist[1/b,Int[( Sin[c+d*x]^j)^(m+j)*Sqrt[a+b* Sin[c+d*x]^(-1)],x]] - 
  Dist[a/b,Int[( Sin[c+d*x]^j)^(m+j)/Sqrt[a+b* Sin[c+d*x]^(-1)],x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2] && ZeroQ[a^2-b^2] && RationalQ[m] && j*m==-3/2

Int[( Sin[c_.+d_.*x_]^j_.)^m_/Sqrt[a_+b_.* Sin[c_.+d_.*x_]^(-1)],x_Symbol] :=
(Print["Int(30th)@(sin^j)^m (a+a sin^k)^n.m"];
  -2*Cos[c+d*x]/(d*(Sin[c+d*x]^j)^m*Sqrt[a+b*Csc[c+d*x]]) - 
  Dist[a/b,Int[1/(( Sin[c+d*x]^j)^m*Sqrt[a+b* Sin[c+d*x]^(-1)]),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2] && ZeroQ[a^2-b^2] && RationalQ[m] && j*m==1/2

Int[( Sin[c_.+d_.*x_]^j_.)^m_*(a_+b_.* Sin[c_.+d_.*x_]^(-1))^(3/2),x_Symbol] :=
(Print["Int(31th)@(sin^j)^m (a+a sin^k)^n.m"];
  -2*a^2*Cos[c+d*x]/(d*(Sin[c+d*x]^j)^m*Sqrt[a+b*Csc[c+d*x]]) + 
  Dist[b,Int[Sqrt[a+b* Sin[c+d*x]^(-1)]/( Sin[c+d*x]^j)^m,x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2] && ZeroQ[a^2-b^2] && RationalQ[m] && j*m==1/2

Int[( Sin[c_.+d_.*x_]^j_.)^m_*(a_+b_.* Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(32th)@(sin^j)^m (a+a sin^k)^n.m"];
  Dist[(Sin[c+d*x]^j)^m*Sqrt[b+a*Sin[c+d*x]]/Sqrt[a+b*Csc[c+d*x]],
    Int[(b+a* Sin[c+d*x])^n/ Sin[c+d*x]^(n+1/2),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && j*m==-1/2 && n^2==1/4

Int[1/(Sqrt[ Sin[c_.+d_.*x_]^(-1)]*Sqrt[a_+b_.* Sin[c_.+d_.*x_]]),x_Symbol] :=
(Print["Int(33th)@(sin^j)^m (a+a sin^k)^n.m"];
  Dist[1/b,Int[Sqrt[ Sin[c+d*x]^(-1)]*Sqrt[a+b* Sin[c+d*x]],x]] - 
  Dist[a/b,Int[Sqrt[ Sin[c+d*x]^(-1)]/Sqrt[a+b* Sin[c+d*x]],x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2]

Int[Sqrt[ Sin[c_.+d_.*x_]^(-1)]*(a_+b_.* Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(34th)@(sin^j)^m (a+a sin^k)^n.m"];
  Dist[Sqrt[Csc[c+d*x]]*Sqrt[Sin[c+d*x]],Int[(a+b* Sin[c+d*x])^n/Sqrt[ Sin[c+d*x]],x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n^2==1/4

Int[( Sin[c_.+d_.*x_]^j_.)^m_*Sqrt[a_+b_.* Sin[c_.+d_.*x_]^k_.],x_Symbol] :=
(Print["Int(35th)@(sin^j)^m (a+a sin^k)^n.m"];
  -2*a*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*Sqrt[a+b*Sin[c+d*x]^k])) /;
FreeQ[{a,b,c,d,m},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && ZeroQ[2*j*k*m+k+2]

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*Sqrt[a_+b_.* Sin[c_.+d_.*x_]^k_.],x_Symbol] :=
(Print["Int(36th)@(sin^j)^m (a+a sin^k)^n.m"];
  2*a*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)/(d*(2*j*k*m+k+1)*Sqrt[a+b*Sin[c+d*x]^k]) + 
  Dist[b*(2*j*k*m+k+2)/(a*(2*j*k*m+k+1)),Int[( Sin[c+d*x]^j)^(m+j*k)*Sqrt[a+b* Sin[c+d*x]^k],x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m] && 
  j*k*m<=-1 && NonzeroQ[2*j*k*m+k+2]

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*Sqrt[a_+b_.* Sin[c_.+d_.*x_]^k_.],x_Symbol] :=
(Print["Int(37th)@(sin^j)^m (a+a sin^k)^n.m"];
  -2*b*Cos[c+d*x]*(Sin[c+d*x]^j)^m/(d*k*(2*j*m+1)*Sqrt[a+b*Sin[c+d*x]^k]) + 
  Dist[a*(2*j*k*m+k-1)/(b*k*(2*j*m+1)),Int[( Sin[c+d*x]^j)^(m-j*k)*Sqrt[a+b* Sin[c+d*x]^k],x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m] && 
  NonzeroQ[2*j*m+1] && j*k*m>0 && j*k*m!=1 && j*k*m!=2

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(38th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(n+1)) + 
  Dist[a*n/(b*(n+1)),Int[( Sin[c+d*x]^j)^(m+j*k)*(a+b* Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  ZeroQ[j*k*m+n+(k+3)/2] && n>-1 && n!=1 && n!=2

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(39th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(2*n+1)) + 
  Dist[n/(a*(2*n+1)),Int[( Sin[c+d*x]^j)^m*(a+b* Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  ZeroQ[j*k*m+n+(k+3)/2] && j*k*m!=1 && j*k*m!=2 && n<-1

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(40th)@(sin^j)^m (a+a sin^k)^n.m"];
  -a*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-1)/(d*n) + 
  Dist[b*(2*n-1)/n,Int[( Sin[c+d*x]^j)^(m+j*k)*(a+b* Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  ZeroQ[j*k*m+n+(k+1)/2] && n>0 && n!=1/2 && n!=1 && n!=2

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(41th)@(sin^j)^m (a+a sin^k)^n.m"];
  a*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^n/(b*d*(2*n+1)) + 
  Dist[(n+1)/(b*(2*n+1)),Int[( Sin[c+d*x]^j)^(m-j*k)*(a+b* Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  ZeroQ[j*k*m+n+(k+1)/2] && j*k*m!=1 && j*k*m!=2 && n<-1

Int[(a_+b_.* Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(42th)@(sin^j)^m (a+a sin^k)^n.m"];
  b*Cos[c+d*x]*(a+b*Sin[c+d*x])^n/(a*d*(2*n+1)) +
  Dist[(n+1)/(a*(2*n+1)),Int[(a+b* Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[ Sin[c_.+d_.*x_]^(-1)*(a_+b_.* Sin[c_.+d_.*x_]^(-1))^n_,x_Symbol] :=
(Print["Int(43th)@(sin^j)^m (a+a sin^k)^n.m"];
  b*Cot[c+d*x]*(a+b*Csc[c+d*x])^n/(a*d*(2*n+1)) + 
  Dist[(n+1)/(a*(2*n+1)),Int[ Sin[c+d*x]^(-1)*(a+b/ Sin[c+d*x])^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n<-1

Int[(a_+b_.* Sin[c_.+d_.*x_])^n_,x_Symbol] :=
(Print["Int(44th)@(sin^j)^m (a+a sin^k)^n.m"];
  -b*Cos[c+d*x]*(a+b*Sin[c+d*x])^(n-1)/(d*n) +
  Dist[a*(2*n-1)/n,Int[(a+b* Sin[c+d*x])^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>0 && n!=1 && n!=2

Int[ Sin[c_.+d_.*x_]^(-1)*(a_+b_.* Sin[c_.+d_.*x_]^(-1))^n_.,x_Symbol] :=
(Print["Int(45th)@(sin^j)^m (a+a sin^k)^n.m"];
  -b*Cot[c+d*x]*(a+b*Csc[c+d*x])^(n-1)/(d*n) + 
  Dist[a*(2*n-1)/n,Int[ Sin[c+d*x]^(-1)*(a+b* Sin[c+d*x]^(-1))^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && ZeroQ[a^2-b^2] && RationalQ[n] && n>0 && n!=1/2 && n!=1 && n!=2

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(46th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cos[c+d*x]*(Sin[c+d*x]^j)^(m-j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),
    Int[( Sin[c+d*x]^j)^(m-2*j*k)*
      (a*(j*k*m+(k-3)/2)-b*(j*k*m-n+(k-3)/2)* Sin[c+d*x]^k)*(a+b* Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m>1 && j*k*m!=2 && n<=-1

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(47th)@(sin^j)^m (a+a sin^k)^n.m"];
  a*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^n/(b*d*(2*n+1)) + 
  Dist[1/(b^2*(2*n+1)),
    Int[( Sin[c+d*x]^j)^(m-j*k)*
      (-b*(j*k*m+(k-1)/2)+a*(j*k*m+n+(k+1)/2)* Sin[c+d*x]^k)*(a+b* Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  0<j*k*m<1 && n<=-1

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(48th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cos[c+d*x]*(Sin[c+d*x]^j)^(m-j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+n+(k-1)/2)) + 
  Dist[1/(b*(j*k*m+n+(k-1)/2)),
    Int[( Sin[c+d*x]^j)^(m-2*j*k)*(b*(j*k*m+(k-3)/2)+a*n* Sin[c+d*x]^k)*(a+b* Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  NonzeroQ[j*k*m+n+(k-1)/2] && j*k*m>1 && j*k*m!=2 && -1<n<0 && j*k*m-1!=n

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(49th)@(sin^j)^m (a+a sin^k)^n.m"];
  -b^2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-2)/(d*(j*k*m+n+(k-1)/2)) + 
  Dist[a/(j*k*m+n+(k-1)/2),
    Int[( Sin[c+d*x]^j)^m*
      (a*(2*j*k*m+n+k)+b*(2*j*k*m+3*n+k-3)* Sin[c+d*x]^k)*(a+b* Sin[c+d*x]^k)^(n-2),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  NonzeroQ[j*k*m+n+(k-1)/2] && j*k*m>=-1 && j*k*m!=1 && j*k*m!=2 && n>1 && n!=2

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(50th)@(sin^j)^m (a+a sin^k)^n.m"];
  -b*Cos[c+d*x]*(Sin[c+d*x]^j)^m*(a+b*Sin[c+d*x]^k)^(n-1)/(d*(j*k*m+n+(k-1)/2)) + 
  Dist[1/(j*k*m+n+(k-1)/2),
    Int[( Sin[c+d*x]^j)^(m-j*k)*
      (b*(j*k*m+(k-1)/2)+a*(j*k*m+2*n+(k-3)/2)* Sin[c+d*x]^k)*(a+b* Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m>0 && j*k*m!=1 && j*k*m!=2 && 0<n<1 && n!=1/2

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(51th)@(sin^j)^m (a+a sin^k)^n.m"];
  a^2*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-2)/(d*(j*k*m+(k+1)/2)) + 
  Dist[a/(j*k*m+(k+1)/2),
    Int[( Sin[c+d*x]^j)^(m+j*k)*
      (b*(2*j*k*m-n+k+3)+a*(2*j*k*m+n+k)* Sin[c+d*x]^k)*(a+b* Sin[c+d*x]^k)^(n-2),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m<-1 && n>1 && n!=2

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(52th)@(sin^j)^m (a+a sin^k)^n.m"];
  a*Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^(n-1)/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(j*k*m+(k+1)/2),
    Int[( Sin[c+d*x]^j)^(m+j*k)*
      (b*(j*k*m-n+(k+3)/2)+a*(j*k*m+n+(k+1)/2)* Sin[c+d*x]^k)*(a+b* Sin[c+d*x]^k)^(n-1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m<-1 && 0<n<1 && n!=1/2

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(53th)@(sin^j)^m (a+a sin^k)^n.m"];
  Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(j*k*m+(k+1)/2)) + 
  Dist[1/(b*(j*k*m+(k+1)/2)),
    Int[( Sin[c+d*x]^j)^(m+j*k)*(-a*n+b*(j*k*m+n+(k+3)/2)* Sin[c+d*x]^k)*(a+b* Sin[c+d*x]^k)^n,x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  NonzeroQ[j*k*m+(k+1)/2] && j*k*m<=-1 && -1<n<0

Int[( Sin[c_.+d_.*x_]^j_.)^m_.*(a_+b_.* Sin[c_.+d_.*x_]^k_.)^n_,x_Symbol] :=
(Print["Int(54th)@(sin^j)^m (a+a sin^k)^n.m"];
  -Cos[c+d*x]*(Sin[c+d*x]^j)^(m+j*k)*(a+b*Sin[c+d*x]^k)^n/(d*(2*n+1)) + 
  Dist[1/(a^2*(2*n+1)),
    Int[( Sin[c+d*x]^j)^m*
      (a*(j*k*m+2*n+(k+3)/2)-b*(j*k*m+n+(k+3)/2)* Sin[c+d*x]^k)*(a+b* Sin[c+d*x]^k)^(n+1),x]]) /;
FreeQ[{a,b,c,d},x] && OneQ[j^2,k^2] && ZeroQ[a^2-b^2] && RationalQ[m,n] && 
  j*k*m<0 && n<=-1
