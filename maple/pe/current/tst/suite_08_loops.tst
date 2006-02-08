#test

# TEST SUITE 8: Loops ################################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "E:\\School\\svn\\thesis\\maple\\pe\\current\\lib":

#######################################################################


iterpow := proc(x, n) local temp;
    temp := 1;
    from 1 to n do
        temp := temp * x;
    end do;
    return temp;
end proc:


goal := proc(x) iterpow(x, 3) end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply));

expected := ToInert(proc(x) local temp1; temp1:=x; temp1:=temp1*x; temp1:=temp1*x; temp1 end proc);

Try(100, got, expected);

#######################################################################

iterpow := proc(x, n) local temp;
    temp := 1;
    from n by -1 to 1 do # looping down
        temp := temp * x;
    end do;
    return temp;
end proc:


goal := proc(x) iterpow(x, 3) end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply));

expected := ToInert(proc(x) local temp1; temp1:=x; temp1:=temp1*x; temp1:=temp1*x; temp1 end proc);

Try(200, got, expected);

#######################################################################

goal := proc()
    x := [];
    for i in [1,2,3,4,5] while i < 4 do
        x := [op(x), i];
    end do;
    x
end proc;

ped := OnPE(goal);
got := ToInert(eval(ped:-ModuleApply));

expected := ToInert(proc () [1, 2, 3] end proc);

Try(300, got, expected);

#######################################################################

oddd := proc(x) type(x, odd) end proc;

p := proc(x) local a, i; 
    a := 1;
    for i from 1 to 10 while oddd(a) do
        a := a + x;
    end do;
    a;
end proc;

goal := proc() p(2) end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc () 21 end proc);

Try(400, got, expected);

#######################################################################

#end test