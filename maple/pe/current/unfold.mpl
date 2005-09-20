

TransformUnfold := module()
    export UnfoldStandalone, UnfoldIntoAssign, RenameAllVariables, RemoveReturns; 
    local addAssigns;

    RenameAllVariables := proc(inert::inert(STATSEQ), genVarName::procedure)
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

        eval(inert, [_Inert_PARAM = rename(_Inert_PARAM), 
                     _Inert_LOCAL = rename(_Inert_LOCAL) ]);
    end proc;


    # Naively removes return statments and replaces them with the expression that was in the return.
    # This will be unsound if the proc is not in if normal form.
    RemoveReturns := proc(inert::inert(STATSEQ))
        eval(inert, [_Inert_RETURN = (() -> args)]); 
    end proc;


    # Just renames variables and removes return statments.
    # Will be unsound if the procedure contains a return within a dynamic if within a loop.
    UnfoldStandalone := RemoveReturns @ RenameAllVariables;


    # For now only supports single assigment, multiple assignment should be trivial.
    # Requires input to be in if normal form.
    UnfoldIntoAssign := proc(body::inert(STATSEQ), genVarName::procedure, x::string)
        local newbody;
        newbody := RenameAllVariables(body, genVarName);
        newbody := RemoveReturns(newbody);       
        addAssigns(newbody, x);
    end proc;


    # assumes returns have been removed
    addAssigns := proc(inert::inert, x::string) local last, res;
        header := getHeader(inert);

        if header = _Inert_STATSEQ then
            last := nops(inert);
            while last > 0 do
                res := procname(op(last,inert), x);
                if res = EMPTY then
                    last := last - 1;
                else
                    return _Inert_STATSEQ(op(1..last-1, inert), res);
                end if;
            end do;
            return EMPTY;
            
        elif header = _Inert_IF then
            map(addAssigns, inert, x);

        elif header = _Inert_CONDPAIR then
            _Inert_CONDPAIR(op(1, inert), procname(op(2, inert), x));

        elif header = _Inert_ASSIGN then
            _Inert_STATSEQ(inert, _Inert_ASSIGN(_Inert_LOCAL(x), op(1, inert)));

        # need to add support for loops and other structures

        else #its an expression
            _Inert_ASSIGN(_Inert_LOCAL(x), inert);
        end if;
    end proc;


end module;
