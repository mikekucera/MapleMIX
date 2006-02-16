with(Domains):
interface(verboseproc=3):
interface(labelling=false):

#xx := proc() local C,x,m,m2;
#   C := DUP(Q,x);
#   m := C[Input](x^4-10*x^2+1);
#   m2 := C[`^`](m,2);
#   return C[Output](m2);
#end proc;

with(PEOptions):

opts := PEOptions();
#opts:-addFunction(PURE, Domains:-UnivariatePolynomial:-ModuleApply);

#opts:-addFunction(PURE, Domains:-EuclideanDomain):
#opts:-addFunction(PURE, Domains:-UniqueFactorizationDomain):
#opts:-addFunction(PURE, Domains:-GcdDomain):
#opts:-addFunction(PURE, Domains:-IntegralDomain):
#opts:-addFunction(PURE, Domains:-CommutativeRing):
#opts:-addFunction(PURE, Domains:-Ring):

opts:-addFunction(PURE, Domains:-RepeatedSquaring):

xx := proc() local C,x,m,m2;
    C := DUP(Q,x);
    m := C[Input](x^4-10*x^2+1);
    return m;
    #m2 := C[`^`](m,2);
    #return C[Output](m2);
end proc;


#xx();


ps := OnPE(xx, opts):



interface(verboseproc=3):
#print(eval(ps:-ModuleApply));

printmod(ps);

G := ps();
#gm := G[Input](x^4-10*x^2+1);
#gm2 := G[`^`](gm,2);
#G[Output](gm2);
