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

p := proc() local t,s;
    t := table();
    t[1] := 99;
    s := t;
    s[2] := 100;
    t[1], t[2];
end proc;

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 99, 100 end proc);

Test(501, got, expected);


p := proc()
    t := table();
    l := [t];
    q := l[1];
    q[1] := 99;
    t[1];
end proc:

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 99 end proc);

Test(502, got, expected);

####################################################################
# in this case x is not a table, it should still work

p := proc () local x; 
    x := [1, 2, 3, 4]; 
    x[3] 
end proc;

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 3 end proc);

Test(601, got, expected);

####################################################################


p := proc() local t;
    t["a"] := 1;
    t["b"] := 2;
    g(t);
    t["a"], t["b"], t["c"];
end proc;

g := proc(t)
    t["c"] := 3;
end proc;

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 1,2,3 end proc);

Test(701, got, expected);

####################################################################

p := proc() local t;
    t := table();
    t["a"] := 66;
    g(t);
    t["a"], t["b"]
end proc;

g := proc() h(args); end proc;

h := proc(t) t["b"] := 77; end proc;


ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 66,77 end proc);

Test(801, got, expected);


####################################################################

#end test
