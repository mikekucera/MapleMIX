#test

# TEST SUITE 4: ARGS ##################################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":

# Test 1 ###############################################################

p:= proc()
    args[1], args[2], args[3], args[4], nargs;
end proc;

goal := proc()
    p(1,2,3,4);
end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply)):
expected := _Inert_PROC(_Inert_PARAMSEQ(), _Inert_LOCALSEQ(), _Inert_OPTIONSEQ(), _Inert_EXPSEQ(), _Inert_STATSEQ(_Inert_INTPOS(1), _Inert_INTPOS(2), _Inert_INTPOS(3), _Inert_INTPOS(4), _Inert_INTPOS(4)), _Inert_DESCRIPTIONSEQ(), _Inert_GLOBALSEQ(), _Inert_LEXICALSEQ(), _Inert_EOP(_Inert_EXPSEQ(_Inert_INTPOS(0))));

Try(100, got, expected);

########################################################################


#end test
