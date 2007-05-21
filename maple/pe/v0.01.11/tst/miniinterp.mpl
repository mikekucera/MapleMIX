libname := libname, "../lib": 

mminterp := mmProgram(

    mmDef("evalProg", mmParams("prog", "input"),
        mmBlock(
            mmAssign("defs", mmTable()),
            mmForeach(mmVar("d"), mmVar("prog"),
                mmTableAssign("defs", mmOp(mmInt(1), mmVar("d")), mmVar("d"))
            ),
            mmExpr(mmCall("evalStat", mmArgs(mmOp(mmInt(3), mmOp(mmInt(1), mmVar("prog"))), mmVar("input"), mmVar("defs"))))
        )
    ),
    
    mmDef("evalStat", mmParams("s", "env", "defs"),
        mmBlock(
            mmAssign("h", mmOp(mmInt(0), mmVar("s"))),
            
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmAssign')),
                mmTableAssign("env", mmOp(mmInt(1), mmVar("s")), 
                    mmCall("evalExpr", mmArgs(mmOp(mmInt(2), mmVar("s")), mmVar("env"), mmVar("defs")))),
                    
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmTableAssign')),
                mmBlock(
                    mmAssign("i", mmCall("evalExpr", mmArgs(mmOp(mmInt(2), mmVar("s")), mmVar("env"), mmVar("defs")))),
                    mmAssign("t", mmLookup(mmVar("env"), mmOp(mmInt(1), mmVar("s")))),
                    mmTableAssign("t", mmOp(mmInt(3), mmVar("s")), 
                        mmCall("evalExpr", mmArgs(mmOp(mmInt(3), mmVar("s")), mmVar("env"), mmVar("defs"))))    
                ),
                
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmIfElse')),
                mmBlock(
                    mmAssign("c", mmCall("evalExpr", mmArgs(mmOp(mmInt(1), mmVar("s")), mmVar("env"), mmVar("defs")))),
                    mmIfElse(mmVar("c"),
                        mmAssign("i", mmInt(2)),
                        mmAssign("i", mmInt(3))
                    ),
                    mmExpr(mmCall("evalStat", mmArgs(mmOp(mmVar("i"), mmVar("s")), mmVar("env"), mmVar("defs"))))
                ),
                
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmIfElse')),
                mmForeach(mmVar("i"), mmVar("s"),
                    mmExpr(mmCall("evalStat", mmArgs(mmVar("i"), mmVar("env"), mmVar("defs"))))
                ),
            
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmForeach')),
                mmBlock(
                    mmAssign("var", mmOp(mmInt(1), mmVar("s"))),
                    mmAssign("e1", mmCall("evalExpr", mmArgs(mmOp(mmInt(2), mmVar("s")), mmVar("env"), mmVar("defs")))),
                    mmForeach(mmVar("i"), mmVar("e1"),
                        mmBlock(
                            mmTableAssign("env", mmVar("var"), mmVar("i")),
                            mmExpr(mmCall("evalStat", mmArgs(mmOp(mmInt(3), mmVar("s")), mmVar("env"), mmVar("defs"))))
                        )
                    )
                ),
                    
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmExpr')),
                mmExpr(mmCall("evalExpr", mmArgs(mmOp(mmInt(1), mmVar("s")), mmVar("env"), mmVar("defs")))),
                
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmError')),
                mmError(mmOp(mmInt(1), mmVar("s"))),
                mmError("statement form not supported")
            
            )))))))
        )
    ),
    
    mmDef("evalExpr", mmParams("e", "env", "defs"),
        mmBlock(
            mmAssign("h", mmOp(mmInt(0), mmVar("e"))),
            
            mmIfElse(mmBin(mmOr, mmBin(mmOr, mmBin(mmEq, mmVar("h"), mmName('mmInt')), mmBin(mmEq, mmVar("h"), mmName('mmString'))), mmBin(mmEq, mmVar("h"), mmName('mmName'))),
                mmExpr(mmOp(mmInt(1), mmVar("e"))),
                
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmTable')),
                mmExpr(mmTable()),
                
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmVar')),
                mmExpr(mmLookup(mmVar("env"), mmOp(mmInt(1), mmVar("e")))),
                
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmLookup')),
                mmBlock(
                    mmAssign("e1", mmCall("evalExpr", mmArgs(mmOp(mmInt(1), mmVar("e")), mmVar("env"), mmVar("defs")))),
                    mmAssign("e2", mmCall("evalExpr", mmArgs(mmOp(mmInt(2), mmVar("e")), mmVar("env"), mmVar("defs")))),
                    mmExpr(mmLookup(mmVar("e1"), mmVar("e2")))
                ),
              
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmOp')),
                mmBlock(
                    mmAssign("e1", mmCall("evalExpr", mmArgs(mmOp(mmInt(1), mmVar("e")), mmVar("env"), mmVar("defs")))),
                    mmAssign("e2", mmCall("evalExpr", mmArgs(mmOp(mmInt(2), mmVar("e")), mmVar("env"), mmVar("defs")))),
                    mmExpr(mmOp(mmVar("e1"), mmVar("e2")))
                ),
                 
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmBin')),
                mmBlock(
                    mmAssign("o", mmOp(mmInt(1), mmVar("e"))),
                    mmAssign("e1", mmCall("evalExpr", mmArgs(mmOp(mmInt(2), mmVar("e")), mmVar("env"), mmVar("defs")))),
                    mmAssign("e2", mmCall("evalExpr", mmArgs(mmOp(mmInt(3), mmVar("e")), mmVar("env"), mmVar("defs")))),
                    mmExpr(mmCall("evalBin", mmArgs(mmVar("o"), mmVar("e1"), mmVar("e2"))))
                ),
                   
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmUn')),
                mmBlock(
                    mmAssign("o", mmOp(mmInt(1), mmVar("e"))),
                    mmAssign("e1", mmCall("evalExpr", mmArgs(mmOp(mmInt(2), mmVar("e")), mmVar("env"), mmVar("defs")))),
                    mmExpr(mmCall("evalUn", mmArgs(mmVar("o"), mmVar("e1"))))
                ),
           
                
            mmIfElse(mmBin(mmEq, mmVar("h"), mmName('mmCall')),
                mmBlock(
                    mmAssign("def", mmLookup(mmVar("defs"), mmOp(mmInt(1), mmVar("e")))),
                    mmAssign("ags", mmOp(mmInt(2), mmVar("e"))),
                    mmAssign("i", mmInt(1)),
                    mmAssign("newEnv", mmTable()),
                    mmForeach(mmVar("param"), mmOp(mmInt(2), mmVar("def")),
                        mmBlock(
                            mmTableAssign("newEnv", mmVar("param"),
                                mmCall("evalExpr", mmArgs(mmOp(mmVar("i"), mmVar("ags")), mmVar("env"), mmVar("defs")))),
                            mmAssign("i", mmBin(mmPlus, mmVar("i"), mmInt(1)))
                        )
                    ),
                    mmExpr(mmCall("evalStat", mmArgs(mmOp(mmInt(3), mmVar("def")), mmVar("newEnv"), mmVar("defs"))))
                ),
                
                mmError("unknown expression form")
            
            ))))))))
        )    
    ),

    mmDef("evalBin", mmParams("mm", "e1", "e2"),
        mmIfElse(mmBin(mmEq, mmVar("mm"), mmName('mmEq')),
            mmExpr(mmBin(mmEq, mmVar("e1"), mmVar("e2"))),
            
        mmIfElse(mmBin(mmEq, mmVar("mm"), mmName('mmPlus')),
            mmExpr(mmBin(mmPlus, mmVar("e1"), mmVar("e2"))),
            
        mmIfElse(mmBin(mmEq, mmVar("mm"), mmName('mmMinus')),
            mmExpr(mmBin(mmMinus, mmVar("e1"), mmVar("e2"))),
            
        mmIfElse(mmBin(mmEq, mmVar("mm"), mmName('mmTimes')),
            mmExpr(mmBin(mmTimes, mmVar("e1"), mmVar("e2"))),
            
        mmIfElse(mmBin(mmEq, mmVar("mm"), mmName('mmAnd')),
            mmExpr(mmBin(mmAnd, mmVar("e1"), mmVar("e2"))),
        
        mmIfElse(mmBin(mmEq, mmVar("mm"), mmName('mmOr')),
            mmExpr(mmBin(mmOr, mmVar("e1"), mmVar("e2"))),
            
            mmError("unknown bin op")
        ))))))
    ),
    
    
    mmDef("evalUn", mmParams("mm", "e1"),
        mmIfElse(mmBin(mmEq, mmVar("mm"), mmName('mmNot')),
            mmExpr(mmUn(mmNot, mmVar("e1"))),
        
        mmIfElse(mmBin(mmEq, mmVar("mm"), mmName('mmNeg')),
            mmExpr(mmUn(mmNeg, mmVar("e1"))),
            
            mmError("unknown un op")
        ))
    )
    
):

simple := mmProgram(
    mmDef("f", mmParams("x", "y"),
        mmExpr(mmBin(mmPlus, mmVar("x"), mmVar("y")))
    )
):


runit := proc() local m, t;
    m["x"] := 10;
    m["y"] := 9;
    t["prog"] := simple;
    t["input"] := m;
    
    MiniMapleInterpreter(mminterp, t);
end proc:

runit();


goal := proc(x) local m, t;
    m["x"] := 10;
    m["y"] := 9;
    t["prog"] := simple;
    t["input"] := m;
    
    MiniMapleInterpreter(mminterp, t);
end proc:

opts := PEOptions();
opts:-setConsiderExpseq(false);
opts:-setIgnoreCommands(false);
ps := OnPE(goal, opts);

printmod(ps);

