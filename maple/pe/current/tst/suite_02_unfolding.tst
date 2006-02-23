#test

# TEST SUITE 2: UNFOLDING  ############################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "../lib":

# TEST 1 ##############################################################

# First occurance of f should unfold because its body reduces to a static expression.
# Second occurance should residualize because its in a dynamic conditional.

p := proc(d, x, y)
    if d then
        f(x,y);
    else
        f(x,d);
    end if;
end proc;

f := proc(x,y) x + y end proc;

goal := proc(d) p(d, 1, 2) end proc;

ped := OnPE(goal);

Try(101, nops([op(3, eval(ped))]), 1); # there should be only one local

got := op(5, ToInert(eval(ped['ModuleApply']))):
expected := _Inert_STATSEQ(_Inert_IF(
    _Inert_CONDPAIR(_Inert_PARAM(1), _Inert_STATSEQ(_Inert_INTPOS(3))),
    _Inert_STATSEQ(_Inert_FUNCTION(_Inert_LEXICAL_LOCAL(1),
                                   _Inert_EXPSEQ(_Inert_PARAM(1))))));


Try(102, got, expected);

f_2 := op(5, ToInert(eval(ped['f_2'])));
expected := _Inert_STATSEQ(_Inert_SUM(_Inert_INTPOS(1), _Inert_PARAM(1)));

Try(103, f_2, expected);

# TEST 2 ##############################################################

p := proc(d, x, y) local r;
    if d = x then
        r := f(x,y); # should residualize to 3
    else
        f(x,d + x); # should residualize to f_2(d+1);
    end if;
end proc;


f := proc(x,y) x+y end proc;

goal := proc(d)
    p(d, 1, 2);
end proc;


ped := OnPE(goal);

Try(201, nops([op(3, eval(ped))]), 1); # there should be only one local

got := op(5, ToInert(eval(ped['ModuleApply']))):
expected :=_Inert_STATSEQ(_Inert_IF(_Inert_CONDPAIR(
  _Inert_EQUATION(_Inert_PARAM(1), _Inert_INTPOS(1)),
  _Inert_STATSEQ(_Inert_INTPOS(3))), _Inert_STATSEQ(_Inert_FUNCTION(
  _Inert_LEXICAL_LOCAL(1),
  _Inert_EXPSEQ(_Inert_SUM(_Inert_INTPOS(1), _Inert_PARAM(1)))))));


Try(202, got, expected);

f_2 := op(5, ToInert(eval(ped['f_2'])));
expected := _Inert_STATSEQ(_Inert_SUM(_Inert_INTPOS(1), _Inert_PARAM(1)));

Try(203, f_2, expected);


# TEST 3 ##############################################################
# let insertion

p := proc(d, x, y) local r;
    f(d + y,d + x);
end proc;

f := proc(x,y) x+y end proc;

goal := proc(d)
    p(d, 1, 2);
end proc;

opts := PEOptions();
opts:-setConsiderExpseq(false);
ped := OnPE(goal, opts);

got := ToInert(eval(ped['ModuleApply'])):
expected := ToInert(proc (d) local x1, y1; x1 := d+2; y1 := d+1; x1+y1 end proc);

Try(301, got, expected);


ped := OnPE(goal, ['noexpseq'=false]);

got := op(5, ToInert(eval(ped['ModuleApply']))):
expected := _Inert_STATSEQ(_Inert_FUNCTION(_Inert_LEXICAL_LOCAL(1),_Inert_EXPSEQ(_Inert_SUM(_Inert_PARAM(1),_Inert_INTPOS(2)),_Inert_SUM(_Inert_INTPOS(1),_Inert_PARAM(1)))));

Try(302, got, expected);

got := ToInert(eval(ped['f_1'])):
expected := ToInert(proc (x, y) x+y end proc);

Try(303, got, expected);


# TEST 4 ##############################################################


p := proc(d, x, y) local r;
    r := f(d, x, y);
    return r;
end proc;

f := proc(d, x, y)
    if d = x then
        x * d;
    else
        y * d;
    end if;
end proc;

goal := proc(d) p(d, 3, 2) end proc;

ped := OnPE(goal);

got :=  op(5, ToInert(eval(ped[ModuleApply])));

expected :=  _Inert_STATSEQ(_Inert_IF(_Inert_CONDPAIR(
  _Inert_EQUATION(_Inert_PARAM(1), _Inert_INTPOS(3)), _Inert_STATSEQ(
  _Inert_ASSIGN(_Inert_LOCAL(1), _Inert_PROD(_Inert_PARAM(1), _Inert_INTPOS(3))
  ))), _Inert_STATSEQ(_Inert_ASSIGN(_Inert_LOCAL(1),
  _Inert_PROD(_Inert_PARAM(1), _Inert_INTPOS(2))))),
  _Inert_ASSIGN(_Inert_LOCAL(2), _Inert_LOCAL(1)), _Inert_LOCAL(2));

Try(401, got, expected);


# TEST 5 ##############################################################

p := proc(a, b) local t;
    t := table();
    t[munge] := proc(x, y) local l;
         l := x * x;
         l := l * y * y;
         return l;
    end proc;
    t[munge](a,b);
end proc;

goal := proc(d) p(3,d) end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply));
expected := _Inert_PROC(_Inert_PARAMSEQ(_Inert_NAME("d")), _Inert_LOCALSEQ(_Inert_NAME("l1")), _Inert_OPTIONSEQ(), _Inert_EXPSEQ(), _Inert_STATSEQ(_Inert_ASSIGN(_Inert_LOCAL(1), _Inert_PROD(_Inert_INTPOS(9), _Inert_PARAM(1), _Inert_PARAM(1))), _Inert_LOCAL(1)), _Inert_DESCRIPTIONSEQ(), _Inert_GLOBALSEQ(), _Inert_LEXICALSEQ(), _Inert_EOP(_Inert_EXPSEQ(_Inert_INTPOS(1))));

Try(501, got, expected);


#######################################################################

m := module() option package;
    local l; export f;
        l := 10;
        f := proc()
            print(l);
        end proc;
end module;


goal := proc() m:-f() end proc;

ped := OnPE(goal);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc () print(10) end proc);

Try(601, got, expected);


#######################################################################
# not really unfolding, more a test of closures

p := proc() local x, mul, l, l1, l2;
    x := 2;
    mul := a -> x * a;
    l := [1,2,3];
    l1 := map(mul, l);
    x := 3;
    l2 := map(mul, l);
    l3 := mul(10);
    [op(l1), op(l2), l3];
end proc;

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() [2,4,6,3,6,9,30] end proc);

Try(701, got, expected);


p := proc(v) local x, mul, l, l3;
    x := 2;
    mul := (a,b) -> x * a * b;
    l3 := mul(10, v);
    l3;
end proc;

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc(v) local l3; l3:=20*v; l3 end proc);

Try(702, got, expected);


p := proc() local x, mul;
    x := 2;
    mul := (a,b) -> x * a * b;
    map(curry(mul, 10), [1,2,3]);
end proc;

ped := OnPE(p);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() [20,40,60] end proc);


Try(703, got, expected);

#######################################################################


p := proc(x, {a:=100}, y) x,y,a end proc;
goal1 := proc() p(1,2,3) end proc;
goal2 := proc() p(1,2,a=3) end proc;

ped := OnPE(goal1);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 1,2,100 end proc);
Try(801, got, expected);


ped := OnPE(goal2);

got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 1,2,3 end proc);
Try(802, got, expected);


#######################################################################

p := proc(d)
    if d then
        return 4;
    end if;
    if d then
        return 6;
    end if;
end proc;

goal := proc(d) local x;
    x := p(d);
end proc;

ped := OnPE(goal);

Try(901, ped(true), p(true));
Try(902, ped(false), p(false));


#######################################################################

#end test
