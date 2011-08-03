(* ::Package:: *)

Int[x_^p_ (a_ x_^n_+b_ x_^(m_ n_+n_+p_+1))^m_, x_] := (x^(-(1+m) n) (x^n (a+b x^(1+m n+p)))^(1+m))/(b (1+m) (1+m n+p))/;FreeQ[{a,b,m,n,p},x]&&NonzeroQ[b*(1+m)*(1+m*n+p)]


Int[(a_+b_ x_)^(n_-1) (c_+d_ (a_+b_ x_)^n_)^m_, x_] := (c+d (a+b x)^n)^(1+m)/(b d (1+m) n)/;FreeQ[{a,b,c,d,m,n},x]&&NonzeroQ[b*d*(1+m)*n]
