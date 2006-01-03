#test

# TEST SUITE 2: TABLES ############################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "E:\\School\\svn\\thesis\\maple\\pe\\current\\lib":

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

p := proc(x, y, d) local t;
    t["x"] := d;
    t["y"] := d;
    if x = y then
        t["compare"] := "equals";
    else
        t["compare"] := "ne";
    end if;
    return t;
end proc;

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc (x, y, d) local t; t["x"] := d; t["y"] := d; if x = y then t["compare"] := "equals"; return t else t["compare"] := "ne"; return t end if end proc);

Test(400, got, expected);

goal := proc(d) p(1,1,d) end proc;


ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc (d) local t1; t1["x"] := d; t1["y"] := d; t1["compare"] := "equals"; t1 end proc);

Test(401, got, expected);

####################################################################


#end test
