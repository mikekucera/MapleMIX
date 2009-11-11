#test

# TEST SUITE 1: BINARY POWERING #######################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "../lib":

pow := proc(x, n)
    if n = 0 then
        return 1;
    else
        return x * pow(x, n-1);
    end if;
end proc:

pow2 := proc(x, n) local y;
   if n=0 then 1
   elif n=1 then x
   elif (n mod 2 = 0) then
        y := pow2(x, n/2);
        y*y;
   else x*pow2(x, n-1)
   end if;
end proc:


# TEST 1 ##############################################################

goal := proc(x)
    pow(x, 3);
end proc:

ped := OnPE(goal):

got := eval(ped[ModuleApply]):

expected := proc(x) x*x*x end proc;

Try(100, ToInert(eval(got)), ToInert(eval(expected)));


# TEST 2 ##############################################################

goal := proc(x)
    pow(x, 1);
end proc:

ped := OnPE(goal):

got := (eval(ped:-ModuleApply)):
expected := proc(x) x end;

Try(200, ToInert(eval(got)), ToInert(eval(expected)));

# TEST 3 ##############################################################


goal := proc(x)
    pow(x, 0);
end proc:

ped := OnPE(goal):

got := (eval(ped:-ModuleApply)):
expected := proc(x) 1 end:

Try(300, ToInert(eval(got)), ToInert(eval(expected)));

# TEST 4 ##############################################################

goal := proc(x)
    pow2(x, 6);
end proc:

ped := OnPE(goal):

got := eval(ped:-ModuleApply);
expected := proc (x) local y1, y2; y1 := x; y2 := x*y1*y1; y2*y2 end proc;

Try(400, ToInert(eval(got)), ToInert(eval(expected)));

# Test 5: nothing to do with bp #######################################

goal := proc(d) local x;
    x := 1;
    x := x + d;
    return x;
end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply));

expected := ToInert(proc(d) local x; x := 1 + d; return x end proc);


Try(500, got, expected);

#######################################################################

goal := proc(n)
    pow(6, n)
end proc;

ped := OnPE(goal);

expected := module () local pow_1; export ModuleApply; 
   pow_1 := proc (n) if n = 0 then return 1 else return 6*pow_1(n-1) end if end proc; 
   ModuleApply := proc (n) pow_1(n) end proc; 
end module;

# helper routine
clean := proc(x) 
    eval(ToInert(eval(x)),_Inert_ASSIGNEDLOCALNAME =
        (proc(a,b,c) procname(a,b) end)) end:
Try(600, clean(ped), clean(expected));

#######################################################################

p := proc(d) local x;
    if d then
        if d then
            x := 1;
            print(x);
        else
            x := 2;
        end if;
        print(x*10);
    else
        x := 3;
    end if;
    print(x*100);
end proc:

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));

expected := ToInert(
    proc (d) 
        if d then  
            if d then 
                print(1); 
                print(10); 
                print(100) 
            else 
                print(20); 
                print(200) 
            end if 
        else 
            print(300) 
        end if 
    end proc
);

Try(700, got, expected);

#######################################################################
#end test
