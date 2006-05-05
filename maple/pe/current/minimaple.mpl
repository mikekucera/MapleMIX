
MiniMapleInterpreter := module() option package;
    export 
        ModuleApply;
    local
        evalProg, evalStat, evalExpr, evalBin, evalUn;
    
    ModuleApply := evalProg;

    evalProg := proc(prog, input) local defs, d;
        defs := table();
        for d in prog do
            defs[op(1,d)] := d;
        end do;
        evalStat(op(3,op(1,prog)), input, defs);
    end proc;
    
    evalStat := proc(s, env, defs) local h, i, t, c, var, e1;
        h := op(0, s);
        if h = mmIfElse then
            &onpe("lprint", "evalStat", "mmIfElse");
            c := evalExpr(op(1,s), env, defs);
            &onpe("lprint", "conditional evaluated");
            if c then
                evalStat(op(2,s), env, defs);
            else
                evalStat(op(3,s), env, defs);
            end if;
        elif h = mmBlock then
            &onpe("lprint", "evalStat", "mmBlock");
            for i in s do
                evalStat(i, env, defs);
            end do;
        elif h = mmExpr then
            &onpe("lprint", "evalStat", "mmExpr");
            evalExpr(op(1,s), env, defs);
        else
            &onpe("lprint", "evalStat", "else");
            error "unknown statement form: %1", h;
        end if;
    end proc;
    
    
    evalExpr := proc(e, env, defs) local h, e1, e2, o, def, ags, newEnv, param, i;
        h := op(0, e);
        if h = mmInt or h = mmString or h = mmName then
            &onpe("lprint", "evalExpr", "mmInt");
            op(1,e);
        elif h = mmVar then
            &onpe("lprint", "evalExpr", "mmVar");
            env[op(1,e)]
        elif h = mmBin then
            &onpe("lprint", "evalExpr", "mmBin");
            o := op(1,e);
            e1 := evalExpr(op(2,e), env, defs);
            e2 := evalExpr(op(3,e), env, defs);
            evalBin(o, e1, e2);
        elif h = mmUn then
            &onpe("lprint", "evalExpr", "mmUn");
            o := op(1,e);
            e1 := evalExpr(op(2,e), env, defs);
            evalUn(o, e1);
        elif h = mmCall then
            &onpe("lprint", "evalExpr", "mmCall");
            def := defs[op(1,e)];
            ags := op(2,e);
            i := 1;
            newEnv := table();
            for param in op(2,def) do
                newEnv[param] := evalExpr(op(i,ags), env, defs);
                &onpe("lprint", "in loop");
                i := i + 1;
            end do;
            &onpe("lprint", "end of mmcall");
            evalStat(op(3,def), newEnv, defs);
        else
            &onpe("lprint", "evalExpr", "else");
            error "unknown expression form: %1", h;
        end if;
    end proc;
    
    evalBin := proc(mm, e1, e2)
        if mm = mmEq      then evalb(e1 = e2)
        elif mm = mmPlus  then e1 + e2
        elif mm = mmMinus then e1 - e2
        elif mm = mmTimes then e1 * e2
        elif mm = mmAnd   then e1 and e2
        elif mm = mmOr    then e1 or e2
        else error "unknown binary operator: %1", mm;
        end if;
    end proc;
    
    evalUn := proc(mm, e1)
        if mm = mmNot   then not e1
        elif mm = mmNeg then -e1
        else error "unknown unary operator: %1", mm;
        end if;
    end proc;

end module: