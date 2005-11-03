
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

        body := eval(m, [MLocal=rename(MGeneratedName), 
                         MParam=rename(MGeneratedName)]);
        return body, names;
    end proc;


    # Naively removes return statments and replaces them with the expression that was in the return.
    # This will be unsound if the proc is not in if-normal form with code below a return removed.
    removeReturns := proc(m::m(StatSeq)) option inline;
        eval(m, [MReturn = MStandaloneExpr]); 
    end proc;


    # TODO: Will be unsound if the procedure contains a return within a dynamic if within a loop.
    # specCall must be the residual call to the specialized procedure, consisting of only dynamic argument expressions,
    # the static ones should have been removed.
    UnfoldStandalone := proc(specProc::m(Proc), specCall::m(Function), genVarName::procedure) ::m(StatSeq);       
        body := ProcBody(specProc);
        params := Params(specProc);        
        body, newNames := renameAllLocals(body, genVarName);
        body := removeReturns(body);
        argExpressions := op(2, specCall);
        
        lets := SimpleQueue();
        i := 1;
        for argExpr in argExpressions while i <= nops(params) do
            if not M:-IsM(argExpr) then next end if;
            
            header := Header(argExpr);
            paramName := op([i,1], params);
            print(header, paramName);
            
            # variables can be substituted directly without fear of duplication
            if member(header, {MParam, MLocal}) then
                body := subs(MParam(paramName) = argExpr, body);            
            else
                let := MAssign(MGeneratedName(newNames[paramName]), argExpr);
                lets:-enqueue(let);
            end if;
            i := i + 1;
            
        end do;

        return MStatSeq(op(lets:-toList()), op(body));       
    end proc;


    # For now only supports single assigment, multiple assignment should be trivial.
    # Requires input to be in if normal form.
    # actually in this case removal of returns isn't needed
    UnfoldIntoAssign := proc(specProc::m(Proc), specCall::m(Function), genVarName::procedure, assignTo::m(GeneratedName)) ::m(StatSeq);
        newbody := UnfoldStandalone(specProc, specCall, genVarName);
        newbody := FlattenStatSeq(newbody);
        
        last  := Last(newbody);        
        if Header(last) = MStandaloneExpr then
            MStatSeq(Front(newbody), MSingleAssign(assignTo, last));
        else
            addAssigns(newbody, op(assignTo));
        end if;
    end proc;


    # assumes returns have been removed and code is in if normal form
    addAssigns := proc(code::m, var::string)
        # TODO need to add support for loops and other structures
        doAdd := proc(c)        
	        header := Header(c);	        	        
	        if header = MStatSeq then	            
	            flat := FlattenStatSeq(c);	            
	            if flat = MStatSeq() then
	                return MStatSeq();
	            end if;
	            MStatSeq(Front(flat), procname(Last(flat)));	
	        elif header = MIfThenElse then
	            MIfThenElse(Cond(c), procname(Then(c)), procname(Else(c)));
	
	        elif header = MAssign then # shouldn't need this
	            MStatSeq(c, MAssign(MGeneratedName(var), op(1, c)));
	        
	        elif header = MStandaloneExpr then
	            MAssign(MGeneratedName(var), op(c));
	            
	        else
	            error cat("addAssigns, not supported yet: ", header);
	        end if;
        end proc;
        
        return doAdd(code);
    end proc;


end module;
