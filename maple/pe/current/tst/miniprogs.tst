#test

# TEST SUITE 1: BINARY POWERING #######################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "../lib":

#######################################################################
# Testing first Futamura projection
# Test: generating a residual program from an interpreter and a source program.
#

power := mmProgram(
    mmDef("pow", mmParams("x", "n"),
        mmIfElse(mmBin(mmEq, mmVar("n"), mmInt(0)),
            mmExpr(mmInt(1)),
            mmExpr(mmBin(mmTimes, mmVar("x"), mmCall("pow", mmArgs(mmVar("x"), mmBin(mmPlus, mmVar("n"), mmInt(-1))))))
        )
    )
);


goal := proc(x) local t;
    t := table();
    t["x"] := x;
    t["n"] := 5;
    MiniMapleInterpreter(power, t);
end proc;

Try(101, goal(3), 243);

opts := PEOptions():
opts:-setConsiderExpseq(false):

ps := OnPE(goal, opts);

got := ToInert(eval(ps:-ModuleApply));

p := proc(x)
local t, e110, newEnv5, e18, newEnv4, e16, newEnv3, e14, newEnv2, e12, e22, e24, e26, e28, e210;
    t["x"] := x;
    e110 := t["x"];
    newEnv5["x"] := t["x"];
    e18 := newEnv5["x"];
    newEnv4["x"] := newEnv5["x"];
    e16 := newEnv4["x"];
    newEnv3["x"] := newEnv4["x"];
    e14 := newEnv3["x"];
    newEnv2["x"] := newEnv3["x"];
    e12 := newEnv2["x"];
    # newEnv1["x"] := newEnv2["x"]; # dead code
    e22 := 1;
    e24 := e12*e22;
    e26 := e14*e24;
    e28 := e16*e26;
    e210 := e18*e28;
    e110*e210
end proc;

expected := ToInert(eval(p));

Try(102, got, expected);

Try(103, ps(3), 243);


#######################################################################

goal2 := proc(x, n) local t;  # fully dynamic
    t := table();
    t["x"] := x;
    t["n"] := n;
    MiniMapleInterpreter(power, t);
end proc;

p := module()
    ModuleApply := proc(x, n) local t; 
        t["x"] := x; 
        t["n"] := n; 
        evalStat_1(t) 
    end proc;
    
    evalStat_1 := proc(env) local e12, c, e16, newEnv1, e14, e22;
        e12 := env["n"];
        c := evalb(e12 = 0);
        if c then 1
        else
            e16 := env["x"];
            newEnv1["x"] := env["x"];
            e14 := env["n"];
            newEnv1["n"] := e14 - 1;
            e22 := evalStat_1(newEnv1);
            e16*e22
        end if
    end proc
end module;

opts := PEOptions():
opts:-setConsiderExpseq(false):

ps := OnPE(goal2, opts);
printmod(ps);

got := op(5, ToInert(eval(ps:-ModuleApply)));
expected := op(5, ToInert(eval(p:-ModuleApply)));

Try(201, got, expected);



got := op(5, ToInert(eval(ps:-evalStat_1)));
expected := op(5, ToInert(eval(p:-evalStat_1)));

Try(202, got, expected);


#######################################################################


#end test
