
Unfold := module()
    export UnfoldStandalone, UnfoldIntoAssign; 
    local addAssigns, removeReturns, renameAllLocals;

    renameAllLocals := proc(m::m(StatSeq), genVarName::procedure)
        local names, rename;
        names := table();

        rename := proc(f)
            proc(n) local newname;
                if assigned(names[n]) then
                    f(names[n]);
                else
                    newname := genVarName();
                    names[n] := newname;
                    f(newname);
                end if;
            end proc;
        end proc;

        eval(m, [MLocal=rename(MLocal), MSingleUse=rename(MSingleUse)]);
    end proc;


    # Naively removes return statments and replaces them with the expression that was in the return.
    # This will be unsound if the proc is not in if-normal form.
    removeReturns := proc(m::m(StatSeq)) option inline;
        eval(m, [MReturn = MStandaloneExpr]); 
    end proc;


    # TODO: Will be unsound if the procedure contains a return within a dynamic if within a loop.
    # specCall must be the residual call to the specialized procedure, consisting of only dynamic argument expressions,
    # the static ones should have been removed.
    UnfoldStandalone := proc(specProc::m(Proc), specCall::m(Function), genVarName::procedure) ::m(StatSeq);       
        body := ProcBody(specProc);
        params := Params(specProc);
        
        body := (removeReturns @ renameAllLocals)(body, genVarName);        
        argExpressions := op(2, specCall);
        
        # process each dynamic argument expression in the function call
        i := 1;
        for argExpr in argExpressions do
            header := Header(argExpr);
            if member(header, {MParam, MLocal}) then       
                body := subs(MParam(op([i,1], params)) = argExpr, body);
            else
                error "only supports dynamic argument expressions that are local variables (for now)";
            end if;
            i := i + 1;
        end do;

        return body;       
    end proc;


    # For now only supports single assigment, multiple assignment should be trivial.
    # Requires input to be in if normal form.
    UnfoldIntoAssign := proc(specProc::m(Proc), specCall::m(Function), genVarName::procedure, assignTo::string) ::m(StatSeq);        
        local newbody;   
        newbody := UnfoldStandalone(specProc, specCall, genVarName);
        addAssigns(newbody, assignTo);
    end proc;


    # assumes returns have been removed
    addAssigns := proc(m::m, x::string) local last, res;
        header := Header(m);
        # TODO, its possible for none of the branches of an if to execute, so need assignment before the if
        # TODO need to add support for loops and other structures
        
        if header = MStatSeq then
            flattened := FlattenStatSeq(m);
            size := nops(flattened);
            res := procname(op(-1, flattened), x);
            MStatSeq(op(1..size-1, flattened), res);

        elif header = MIfThenElse then
            MIfThenElse(Cond(m), procname(Then(m),x), procname(Else(m),x));

        elif header = MAssign then
            MStatSeq(m, MAssign(MLocal(x), op(1, m)));
        
        elif header = MStandaloneExpr then
            MAssign(MLocal(x), op(m));
            
        else
            error cat("addAssigns, not supported yet: ", header);
        end if;
    end proc;


end module;
