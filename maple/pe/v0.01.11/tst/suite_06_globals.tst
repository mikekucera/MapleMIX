#test

# TEST SUITE 5: GLOBALS ############################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "../lib":

# TEST 1 ###########################################################
# very basic

p := proc() global g;
    g := 0;
    NULL;
end proc;

f := proc() global g;
    p();
    g := g + 1;
end proc;

ped := OnPE(f);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() global g; 1 end proc);

Try(100, got, expected);

# TEST 2 ###########################################################
# global tables


f := proc() global t;
    t[1] := 10;
    t[2] := 20;
end proc;

goal := proc()
    f();
    t[1], t[2];
end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 10, 20 end proc);

Try(200, got, expected);


####################################################################


#g := 99;
                            
#p := proc()  global g; local l;
#    l := 'g';
#    g := 100;
#    return eval(l);
#end proc;


#ped := OnPE(p);

#got := ToInert(eval(ped:-ModuleApply));
#expected := ToInert(proc() global g; return 100 end proc);

#Try(300, got, expected);


####################################################################

#end test
