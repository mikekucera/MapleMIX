
MiniMapleInterpreter := module() option package;
    export ModuleApply, evalExpr;
    
    ModuleApply := evalProg;

    evalProg := proc(prog, input)
        defs := table();
        for d in prog do
            defs[op(1,d)] := d;
        end do;
        evalStat(op(3,op(1,prog)), input, defs);
    end proc;
    
    evalStat := proc(s, env, defs)
        h := op(0, s);
        if h = mmAssign then
            env[op(1,s)] := evalExpr(op(2,s), env, defs);
        elif h = mmTableAssign then
            i := evalExpr(op(2,s), env);
            env[op(1,s)][i] := evalExpr(op(3,s), env, defs);
        elif h = mmIfElse then
            c := evalExpr(op(1,s), env, defs);
            if c then
                i := 2
            else
                i := 3
            end if;
            evalStat(op(i,s), env, defs);
        elif h = mmBlock then
            for i in s do
                evalStat(i, env, defs);
            end do;
        elif h = mmForeach then
            var := op(1,s);
            e1 := evalExpr(op(2,s), env, defs);
            for i in e1 do
                env[var] := i;
                evalStat(op(3,s), env, defs);
            end do;
        elif h = mmExpr then
            evalExpr(op(1,s), env, defs);
        else
            error "unknown statement form: %1", h;
        end if;
    end proc;
    
    
    evalExpr := proc(e, env, defs)
        h := op(0, e);
        if h = mmInt or h = mmString then
            op(1,e);
        elif h = mmTable then
            table();
        elif h = mmVar then
            if assigned(env[op(1,e)]) then
                env[op(1,e)]
            else
                error "variable has no value: %1", e;
            end if;
        elif h = mmLookup then
            e1 := evalExpr(op(1,e), env, defs);
            e2 := evalExpr(op(2,e), env, defs);
            e1[e2];
        elif h = mmOp then
            e1 := evalExpr(op(1,e), env, defs);
            e2 := evalExpr(op(2,e), env, defs);
            op(e1, e2);
        elif h = mmBin then
            o := op(1,e);
            e1 := evalExpr(op(2,e), env, defs);
            e2 := evalExpr(op(3,e), env, defs);
            evalBin(o, e1, e2);
        elif h = mmUn then
            o := op(1,e);
            e1 := evalExpr(op(2,e), env, defs);
            getUn(o, e1);
        elif h = mmCall then
            def := defs[op(1,e)];
            ags := op(2,e);
            i := 1;
            newEnv := table();
            for param in op(2,def) do
                newEnv[param] := evalExpr(op(i,ags), env, defs);
                i := i + 1;
            end do;
            evalStat(op(3,def), newEnv, defs);
        else
            error "unknown expression form: %1", h;
        end if;
    end proc;
    
    evalBin := proc(mm, e1, e2)
        if mm = mmEq then 
            e1 = e2
        elif mm = mmPlus then 
            e1 + e2
        elif mm = mmMinus then
            e1 - e2
        elif mm = mmTimes then
            e1 * e2
        else
            error "unknown binary operator: %1", mm;
        end if;
    end proc;
    
    getUn := proc(mm, e1)
        if mm = mmNot then
            not e1
        elif mm = mmNeg then
            -e1
        else
            error "unknown unary operator: %1", mm;
        end if;
    end proc;

end module: