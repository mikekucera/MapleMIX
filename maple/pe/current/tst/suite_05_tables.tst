#test

# TEST SUITE 2: TABLES ############################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":

# TEST 1 ###########################################################
# very basic

p := proc() local x, t;
    x := 99;
    t[5] := x;
    t[5];
end proc;


ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 99 end proc);

Test(100, got, expected);

# TEST 1 ###########################################################
# same thing but with symbols

p := proc() local x, t;
    x := 99;
    t[C] := x;
    t[C];
end proc;


ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 99 end proc);

Test(200, got, expected);



####################################################################

p := proc(d) local t;
    t[1] :=88;
    if d then
        t[1] := 99;
    end if;
    t[1];
end proc;

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc(d) if d then 99 else 88 end if end proc);

Test(300, got, expected);

####################################################################

#end test
