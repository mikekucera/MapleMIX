#test

# TEST SUITE 4: ARGS ##################################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "../lib":

# Test 1 ###############################################################

p:= proc()
    args[1], args[2], args[3], args[4], nargs;
end proc;

goal := proc()
    p(1,2,3,4);
end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply)):
expected := ToInert(proc () 1, 2, 3, 4, 4 end proc);

Try(100, got, expected);



# Test 2 ###############################################################
# let insertion of args and nargs

#p := proc() args[1], args[2], args[3], args[4], nargs end proc;
#goal := proc() p(1,2,args,3) end proc;

#ped := OnPE(goal);

#got := ToInert(eval(ped:-ModuleApply));
#expected := ToInert(proc () local args1, nargs1; args1 := 1, 2, args, 3; nargs1 := nops([args1]); 1, 2, args1[3], args1[4], nargs1 end proc);

#Try(200, got, expected);


# Test 3 ###############################################################

#p := proc() args[1], args[2], args[3], args[4], nargs end proc;

#goal := proc(d) 
#    if d then
#        p(1,2,args,3) 
#    end if;
#end proc;

#ped := OnPE(goal);

#got := op(5, ToInert(eval(ped:-ModuleApply)));
#expected := op(5, ToInert(proc (d) local args1, nargs1; if d then args1 := 1, 2, args, 3; nargs1 := nops([args1]); 1, 2, args1[3], args1[4], nargs1 end if end proc));


#Try(301, got, expected);


########################################################################

p := proc() args end proc;

goal := proc() p(1,2,3,4) end proc;

ped := OnPE(goal);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 1,2,3,4 end proc);
Try(401, got, expected);

########################################################################

p1 := proc() op([args])[1] end proc;
p2 := proc() args[1] end proc;


goal := proc() p1(1,2,3) end proc;
ped := OnPE(goal);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 1 end proc);
Try(501, got, expected);


goal := proc() p1(1) end proc;
ped := OnPE(goal);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() (1)[1] end proc); # important case
Try(501, got, expected);


goal := proc() p2(1,2,3) end proc;
ped := OnPE(goal);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 1 end proc);
Try(501, got, expected);


goal := proc() p2(1) end proc;
ped := OnPE(goal);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 1 end proc);
Try(501, got, expected);

#######################################################################################
#end test
