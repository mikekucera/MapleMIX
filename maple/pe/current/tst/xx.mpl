with(Domains):
interface(verboseproc=3):
interface(labelling=false):

#xx := proc() local C,x,m,m2;
#   C := DUP(Q,x);
#   m := C[Input](x^4-10*x^2+1);
#   m2 := C[`^`](m,2);
#   return C[Output](m2);
#end proc;

with(PEOptions);

opts := PEOptions();
opts:-addFunction(PURE, DUP);

xx := proc() local C,x,m,m2;
    C := DUP(Q,x);
    m := C[Input](x^4-10*x^2+1);
    m2 := C[`^`](m,2);
    return C[Output](m2);
end proc;


xx();


ps := OnPE(xx, opts):



#for procName in map(op, [indices(ps)]) do
#    print(procName);
#    print(op(8, ps[procName]));
#end do;

print("here");

print();
interface(verboseproc=3):
#print(eval(ps:-ModuleApply));

printmod(indices(ps));


#print();
#print();

#ps();
