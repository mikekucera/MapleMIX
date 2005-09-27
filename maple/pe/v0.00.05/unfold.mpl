

TransformUnfold := module()
    export UnfoldStandalone, UnfoldIntoAssign, RenameAllLocals, RemoveReturns; 
    local addAssigns;

    RenameAllLocals := proc(inert::inert(STATSEQ), genVarName::procedure)
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

        eval(inert, [_Inert_LOCAL = rename(_Inert_LOCAL) ]);
    end proc;


    # Naively removes return statments and replaces them with the expression that was in the return.
    # This will be unsound if the proc is not in if-normal form.
    RemoveReturns := proc(inert::inert(STATSEQ))
        eval(inert, [_Inert_RETURN = (() -> args)]); 
    end proc;


    # TODO: Will be unsound if the procedure contains a return within a dynamic if within a loop.
    # specCall must be the residual call to the specialized procedure, consisting of only dynamic argument expressions,
    # the static ones should have been removed.
    UnfoldStandalone := proc(specProc::inert(PROC), specCall::inert(FUNCTION), genVarName::procedure)::inert(STATSEQ);       
        body := getProcBody(specProc);
        body := (RemoveReturns @ RenameAllLocals)(body, genVarName);        

        argExpressions := op(2, specCall);

        # process each dynamic argument expression in the function call
        i := 1;
        for argExpr in argExpressions do
            header := getHeader(argExpr);

            if header = _Inert_LOCAL then                
                body := subs(_Inert_PARAM(i) = _Inert_LOCAL(op(argExpr)), body);
            elif header = _Inert_PARAM then
                body := subs(_Inert_PARAM(i) = _Inert_PARAM(op(argExpr)), body);
            else
                error "only supports dynamic argument expressions that are local variables (for now)";
            end if;
            i := i + 1;
        end do;

        return body;       
    end proc;


    # For now only supports single assigment, multiple assignment should be trivial.
    # Requires input to be in if normal form.
    UnfoldIntoAssign := proc(specProc::inert(PROC), specCall::inert(FUNCTION), genVarName::procedure, assignTo::string)::inert(STATSEQ);
        local newbody;
        newbody := UnfoldStandalone(specProc, specCall, genVarName);
        addAssigns(newbody, assignTo);
    end proc;


    # assumes returns have been removed
    addAssigns := proc(inert::inert, x::string) local last, res;
        header := getHeader(inert);

        if header = _Inert_STATSEQ then
            flattened := flattenStatseq(inert);
            size := nops(flattened);
            res := procname(op(-1, flattened), x);
            _Inert_STATSEQ(op(1..size-1, flattened), res);

        # TODO, its possible for none of the branches of an if to execute, so need assignment before the if

        elif header = _Inert_IF then
            map(addAssigns, inert, x);

        elif header = _Inert_CONDPAIR then
            _Inert_CONDPAIR(op(1, inert), procname(op(2, inert), x));

        elif header = _Inert_ASSIGN then
            _Inert_STATSEQ(inert, _Inert_ASSIGN(_Inert_LOCAL(x), op(1, inert)));

        # TODO need to add support for loops and other structures

        else #its an expression
            _Inert_ASSIGN(_Inert_LOCAL(x), inert);
        end if;
    end proc;


end module;
