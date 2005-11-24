#test

# TEST SUITE 5: GLOBALS ############################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":

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

####################################################################

#end test
