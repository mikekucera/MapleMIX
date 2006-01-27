
MiniMapleInterpreter := module() option package;
    export ModuleApply;
    
    ModuleApply := evalExpr;

    
    evalStat := proc(s, env)
        h := op(0, s);
        if h = mmAssign then
            env[op(1,s)] := evalExpr(op(2,s), env);
        elif h = mmTableAssign then
            i := evalExpr(op(2,s), env);
            env[op(1,s)][i] := evalExpr(op(3,s), env);
        elif h = mmIfElse then
            c := evalExpr(op(1,s), env);
            if c then
                i := 2
            else
                i := 3
            end if;
            evalExpr(op(i,s), env);
        elif h = mmBlock then
            for i in s do
                evalStat(i, env);
            end do;
        elif h = mmForeach then
            var := op(1,s);
            e1 := evalExpr(op(2,s), env);
            for i in e1 do
                env[var] := i;
                evalStat(op(3,s), env);
            end do;
        else
            error "unknown statement form: %1", h;
        end if;
    end proc;
    
    
    evalExpr := proc(e, env)
        h := op(0, e);
        if h = mmInt or h = mmString then
            op(1,e);
        elif h = mmTable then
            table();
        elif h = mmVar then
            env[op(1,e)]
        elif h = mmLookup then
            e1 := evalExpr(op(1,e), env);
            e2 := evalExpr(op(2,e), env);
            e1[e2];
        elif h = mmOp then
            e1 := evalExpr(op(1,e), env);
            e2 := evalExpr(op(2,e), env);
            op(e1, e2);
        elif h = mmBin then
            o := op(1,e);
            e1 := evalExpr(op(2,e), env);
            e2 := evalExpr(op(3,e), env);
            getBin(o)(e1, e2);
        elif h = mmUn then
            o := op(1,e);
            e1 := evalExpr(op(2,e), env);
            getUn(o)(e1);
        else
            error "unknown expression form: %1", h;
        end if;
    end proc;
    
    getBin := proc(mm)
        if mm = mmEq then 
            `=`
        elif mm = mmPlus then 
            `+`
        else
            error "unknown binary operator: %1", mm;
        end if;
    end proc;
    
    getUn := proc(mm)
        if mm = mmNot then
            `not`
        elif mm = mmNeg then
            `-`
        else
            error "unknown unary operator: %1", mm;
        end if;
    end proc;

end module: