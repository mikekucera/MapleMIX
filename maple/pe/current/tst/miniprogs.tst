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

#end test
