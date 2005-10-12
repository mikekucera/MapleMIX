
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

        eval(m, [MLocal=rename(MLocal)]);
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
    UnfoldIntoAssign := proc(specProc::m(Proc), specCall::m(Function), genVarName::procedure, assignTo::m(SingleUse)) ::m(StatSeq);        
        local newbody;   
        newbody := UnfoldStandalone(specProc, specCall, genVarName);
        addAssigns(newbody, assignTo);
    end proc;


    # assumes returns have been removed and code is in if normal form
    addAssigns := proc(code::m, var::m)
    
        doAdd := proc(c)        
	        header := Header(c);
	        # TODO need to add support for loops and other structures
	        
	        if header = MStatSeq then	            
	            flattened := FlattenStatSeq(c);	            
	            if flattened = MStatSeq() then
	                return MStatSeq();
	            end if;	            
	            before := [op(1..-2, flattened)];
	            last := op(-1, flattened);
	            
	            # only need to do this if the if part or else part is empty
	            
	            if Header(last) = MIfThenElse 
	               and nops(before) > 0 
	               and (Then(last) = MStatSeq() or Else(last) = MStatSeq())
	               then
	                sndlast := op(-1, before);
	                before := [op(1..-2, before)];
	                MStatSeq(op(before), procname(sndlast), procname(last));
	            else
	            	MStatSeq(op(before), procname(last));
	            end if;
	
	        elif header = MIfThenElse then
	            print("else", Else(c));
	            MIfThenElse(Cond(c), procname(Then(c)), procname(Else(c)));
	
	        elif header = MAssign then
	            MStatSeq(c, MAssign(var, op(1, c)));
	            
	        elif header = MReturn then
	            MAssign(var, op(c));
	        
	        elif header = MStandaloneExpr then
	            MAssign(var, op(c));
	            
	        else
	            error cat("addAssigns, not supported yet: ", header);
	        end if;
        end proc;
        
        return doAdd(code);
    end proc;


end module;
