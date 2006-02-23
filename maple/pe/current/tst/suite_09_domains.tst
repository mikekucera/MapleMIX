#test

# TEST SUITE 9: Domains ################################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "../lib":

#######################################################################

expected := ToInert(proc() x^8 - 20*x^6+102*x^4 - 20*x^2+1 end proc);


p1 := proc(f) expand(f*f) end;
tab1 := table([Q = p1]);
p2 := proc(idx) tab1[idx] end;



# t = tests
t1 := proc() p1( x^4-10*x^2 +1 ); end;
t2 := proc() local C;
    C := p2(Q);
    C(x^4-10*x^2 +1 );
end;

t3 := proc()
    p2(Q)(x^4-10*x^2 +1 );
end;

t4 := proc()
    tab1[Q](x^4-10*x^2 +1 );
end;


t1s := OnPE(t1);
got := ToInert(eval(t1s:-ModuleApply));
Try(101, got, expected);

t2s := OnPE(t2);
got := ToInert(eval(t2s:-ModuleApply));
Try(102, got, expected);

t3s := OnPE(t3);
got := ToInert(eval(t3s:-ModuleApply));
Try(103, got, expected);

t4s := OnPE(t4);
got := ToInert(eval(t4s:-ModuleApply));
Try(104, got, expected);


#######################################################################

#end test
