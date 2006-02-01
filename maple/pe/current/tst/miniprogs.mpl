
simple := mmProgram(
    mmDef("f", mmParams("x","y"),
        mmExpr(mmBin(mmPlus, mmVar("x"), mmVar("y")))
    )
);

#goal := proc(d) local t;
#    t := table();
#    t["x"] := 6;
#    t["y"] := d;
#    MiniMapleInterpreter(simple, t);
#end proc;


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

goal(3);

opts := PEOptions();
opts:-setConsiderExpseq(false);
ps := OnPE(goal, opts);

printmod(ps);

ps(3);
