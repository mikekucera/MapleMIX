with(Domains):
interface(verboseproc=3):
interface(labelling=false):
kernelopts(opaquemodules=false):
kernelopts(ASSERT=true):

infolevel[PE] := 7:

#xx := proc() local C,x,m,m2;
#   C := DUP(Q,x);
#   m := C[Input](x^4-10*x^2+1);
#   m2 := C[`^`](m,2);
#   return C[Output](m2);
#end proc;

with(PEOptions):

opts := PEOptions();
opts:-addFunction(PURE, Domains:-UnivariatePolynomial:-ModuleApply);

#opts:-addFunction(PURE, Domains:-EuclideanDomain):
#opts:-addFunction(PURE, Domains:-UniqueFactorizationDomain):
#opts:-addFunction(PURE, Domains:-GcdDomain):
#opts:-addFunction(PURE, Domains:-IntegralDomain):
#opts:-addFunction(PURE, Domains:-CommutativeRing):
#opts:-addFunction(PURE, Domains:-Ring):

opts:-addFunction(PURE, Domains:-RepeatedSquaring):

xx := proc() local C23,x56,mmm, nnn;
    C23 := DUP(Q,x56);
    mmm := C23[Input];
    return mmm(x56^4-10*x56^2+1);
    #m2 := C[`^`](m,2);
    #return C[Output](m2);
end proc;

zz :=  proc()
local t;
t := proc(a)
local x;
    if not type(a, function) or
    op(0, a) <> `domains/DenseUnivariatePolynomial/badge0` or nops(a) = 0
    then return false
    end if;
    for x in a do
        if not Domains:-Q[Domains:-Type](x) then return false end if
    end do;
    true
end proc:
t;
end proc;

# yy := proc()
#     Domains:-hasCategory(Domains:-Set, Domains:-Set);
# end proc;

# printlevel := 10000;
# xx();

ps := OnPE(xx, opts);
tracelast;
#ps := OnPE(zz, opts);

#interface(verboseproc=3):
#print(eval(ps:-ModuleApply));

printmod(ps);

# G := ps();
#gm := G[Input](x^4-10*x^2+1);
#gm2 := G[`^`](gm,2);
#G[Output](gm2);
