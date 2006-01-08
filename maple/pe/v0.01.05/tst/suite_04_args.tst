#test

# TEST SUITE 4: ARGS ##################################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "E:\\School\\svn\\thesis\\maple\\pe\\current\\lib":

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

p := proc() args[1], args[2], args[3], args[4], nargs end proc;
goal := proc() p(1,2,args,3) end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc () local args1, nargs1; args1 := 1, 2, args, 3; nargs1 := nops([args1]); 1, 2, args1[3], args1[4], nargs1 end proc);

Try(200, got, expected);


# Test 3 ###############################################################

p := proc() args[1], args[2], args[3], args[4], nargs end proc;

goal := proc(d) 
    if d then
        p(1,2,args,3) 
    end if;
end proc;

ped := OnPE(goal);

got := op(5, ToInert(eval(ped:-ModuleApply)));
expected := _Inert_STATSEQ(_Inert_IF(_Inert_CONDPAIR(_Inert_PARAM(1), _Inert_STATSEQ(_Inert_FUNCTION(_Inert_LEXICAL_LOCAL(1), _Inert_EXPSEQ(_Inert_INTPOS(1), _Inert_INTPOS(2), _Inert_ARGS(), _Inert_INTPOS(3)))))));


Try(301, got, expected);

got := op(5, ToInert(eval(ped:-p_1)));
expected := _Inert_STATSEQ(_Inert_EXPSEQ(_Inert_INTPOS(1), _Inert_INTPOS(2), _Inert_TABLEREF(_Inert_ARGS(), _Inert_EXPSEQ(_Inert_INTPOS(3))), _Inert_TABLEREF(_Inert_ARGS(), _Inert_EXPSEQ(_Inert_INTPOS(4))), _Inert_NARGS()));


Try(302, got, expected);

########################################################################


#end test
