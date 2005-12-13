#test

# TEST SUITE 8: Loops ################################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":

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

#end test