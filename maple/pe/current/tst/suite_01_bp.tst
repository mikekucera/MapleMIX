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

got := ToInert(eval(ped[ModuleApply])):

expected := _Inert_PROC(_Inert_PARAMSEQ(_Inert_NAME("x")),_Inert_LOCALSEQ(),_Inert_OPTIONSEQ(),_Inert_EXPSEQ(),_Inert_STATSEQ(_Inert_PROD(_Inert_PARAM(1),_Inert_PARAM(1),_Inert_PARAM(1))),_Inert_DESCRIPTIONSEQ(),_Inert_GLOBALSEQ(),_Inert_LEXICALSEQ(),_Inert_EOP(_Inert_EXPSEQ(_Inert_INTPOS(1)))):

Try(100, got, expected);


# TEST 2 ##############################################################

goal := proc(x)
    pow(x, 1);
end proc:

ped := OnPE(goal):

got := ToInert(eval(ped:-ModuleApply)):
expected := _Inert_PROC(_Inert_PARAMSEQ(_Inert_NAME("x")),_Inert_LOCALSEQ(),_Inert_OPTIONSEQ(),_Inert_EXPSEQ(),_Inert_STATSEQ(_Inert_PARAM(1)),_Inert_DESCRIPTIONSEQ(),_Inert_GLOBALSEQ(),_Inert_LEXICALSEQ(),_Inert_EOP(_Inert_EXPSEQ(_Inert_INTPOS(1)))):

Try(200, got, expected);

# TEST 3 ##############################################################


goal := proc(x)
    pow(x, 0);
end proc:

ped := OnPE(goal):

got := ToInert(eval(ped:-ModuleApply)):
expected := _Inert_PROC(_Inert_PARAMSEQ(_Inert_NAME("x")),_Inert_LOCALSEQ(),_Inert_OPTIONSEQ(),_Inert_EXPSEQ(),_Inert_STATSEQ(_Inert_INTPOS(1)),_Inert_DESCRIPTIONSEQ(),_Inert_GLOBALSEQ(),_Inert_LEXICALSEQ(),_Inert_EOP(_Inert_EXPSEQ(_Inert_INTPOS(1)))):

Try(300, got, expected);

# TEST 4 ##############################################################

goal := proc(x)
    pow2(x, 6);
end proc:

ped := OnPE(goal):

got := ToInert(eval(ped:-ModuleApply)):
expected := _Inert_PROC(_Inert_PARAMSEQ(_Inert_NAME("x")), _Inert_LOCALSEQ(_Inert_NAME("y1"), _Inert_NAME("y2")), _Inert_OPTIONSEQ(), _Inert_EXPSEQ(), _Inert_STATSEQ(_Inert_ASSIGN(_Inert_LOCAL(1), _Inert_PARAM(1)), _Inert_ASSIGN(_Inert_LOCAL(2), _Inert_PROD(_Inert_PARAM(1), _Inert_LOCAL(1), _Inert_LOCAL(1))), _Inert_PROD(_Inert_LOCAL(2), _Inert_LOCAL(2))), _Inert_DESCRIPTIONSEQ(), _Inert_GLOBALSEQ(), _Inert_LEXICALSEQ(), _Inert_EOP(_Inert_EXPSEQ(_Inert_INTPOS(1)))):

Try(400, got, expected);

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

got := op(5, ToInert(eval(ped:-pow_1)));

expected := _Inert_STATSEQ(_Inert_IF(_Inert_CONDPAIR(_Inert_EQUATION(_Inert_PARAM(1), _Inert_INTPOS(0)), _Inert_STATSEQ(_Inert_RETURN(_Inert_INTPOS(1)))), _Inert_STATSEQ(_Inert_ASSIGN(_Inert_LOCAL(1), _Inert_FUNCTION(_Inert_LEXICAL_LOCAL(1), _Inert_EXPSEQ(_Inert_SUM(_Inert_PARAM(1), _Inert_INTNEG(1))))), _Inert_RETURN(_Inert_PROD(_Inert_LOCAL(1), _Inert_INTPOS(6))))));

Try(600, got, expected);

#######################################################################

#end test
