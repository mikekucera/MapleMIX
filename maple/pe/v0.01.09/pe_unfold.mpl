
Unfold := module()
    export UnfoldStandalone, UnfoldIntoAssign;
    local addAssigns, removeReturns, renameAllLocals;

    renameAllLocals := proc(m::mform(StatSeq), genVarName) local names, rename, body;
        names := table();

        rename := proc(f)
            proc(n) local newname;
                if assigned(names[n]) then
                    f(names[n]);
                else
                    newname := genVarName(n);
                    names[n] := newname;
                    f(newname);
                end if;
            end proc;
        end proc;

        body := eval(m, [MLocal=rename(MGeneratedName),
                         MParam=rename(MGeneratedName)]);
                         # TODO; MSigngleUse = rename(MSingleUse)
                         #MSingleUse=rename(MGeneratedName)]); # ok because MSingleUse is removed by FromM
                         #MSingleUse=rename(MSingleUse)]);
        return body, names;
    end proc;


    # Naively removes return statments and replaces them with the expression that was in the return.
    # This will be unsound if the proc is not in if-normal form with code below a return removed.
    removeReturns := proc(m::mform(StatSeq)) option inline;
        eval(m, [MReturn = MStandaloneExpr]);
    end proc;


    # TODO: Will be unsound if the procedure contains a return within a dynamic if within a loop.
    # specCall must be the residual call to the specialized procedure, consisting of only dynamic argument expressions,
    # the static ones should have been removed.
    UnfoldStandalone := proc(specProc::mform(Proc), specCall::mform(ExpSeq),
                             fullCall::mform(ExpSeq), genVarName) :: mform(StatSeq);
        local body, params, let, lets, i, header, paramName, letArgs, newNames, 
              letNargs, argsName, nargsName, argExpr;
        body := M:-TransformIf:-TransformToReturnNormalForm(ProcBody(specProc));
        params := Params(specProc);
        body, newNames := renameAllLocals(body, genVarName);
        body := removeReturns(body);

        # let insert the variables
        lets := SimpleQueue();
        i := 1;
        for argExpr in specCall while i <= nops(params) do
            if argExpr::Static then next end if;

            header := Header(argExpr);
            paramName := op([i,1], params);
            # variables can be substituted directly without fear of duplication
            # TODO, this won't be needed if we go to a general purpose copy propagator
            if member(header, {MParam, MLocal}) then
                body := subs(MGeneratedName(newNames[paramName]) = argExpr, body);
            else
                # TODO, this is a redundant check, remove eventually
                if isPossibleExpSeq(argExpr) then
                    error "cannot let-insert a dynamic expression if it could possibly be an expression sequence";
                end if;
                let := MAssign(MGeneratedName(newNames[paramName]), argExpr);
                lets:-enqueue(let);                
            end if;
            i := i + 1;
        end do;

        # let insert args and nargs if needed
        letNargs := NULL;
        if M:-UsesNargs(specProc) then
            argsName  := genVarName("args");
            nargsName := genVarName("nargs");
            letNargs :=
                MAssign(MGeneratedName(nargsName),
                        MFunction(MAssignedName("nops", "PROC",
                                                MAttribute(MName("protected", MAttribute(MName("protected"))))),
                                  MExpSeq(MList(MExpSeq(MGeneratedName(argsName))))));
            body := subs(MNargs() = MGeneratedName(nargsName), body);
        end if;

        # let insert nargs if needed
        letArgs := NULL;
        if letNargs <> NULL or M:-UsesArgs(specProc) then
            if not assigned(argsName) then
                argsName := genVarName("args");
            end if;
            letArgs := MAssign(MGeneratedName(argsName), fullCall);
            body := subs(MArgs() = MGeneratedName(argsName), body);
        end if;

        return MStatSeq(op(lets:-toList()), letArgs, letNargs, op(body));
    end proc;



    UnfoldIntoAssign := proc(specProc::mform(Proc), specCall::mform(ExpSeq), fullCall::mform(ExpSeq),
                             genVarName, assignTo::mform({Local, SingleUse})) ::mform(StatSeq);
        local newbody, last;
        newbody := UnfoldStandalone(specProc, specCall, fullCall, genVarName);
        newbody := M:-FlattenStatSeq(newbody);
        
        last  := Last(newbody);
        #if Header(last) = MStandaloneExpr then
        if member(Header(last), {MStandaloneExpr, MStandaloneFunction}) then
            MStatSeq(Front(newbody), MAssign(assignTo, op(last)));
        else
            if assignTo::mform(SingleUse) then
                # conservative
                # this is the place where where a singleuse may be assigned
                # to more than once, convert into a regular GeneratedName
                addAssigns(newbody, MGeneratedName(Name(assignTo)));
            else
                addAssigns(newbody, assignTo);
            end if;
        end if;
    end proc;


    # assumes returns have been removed and code is in if normal form
    addAssigns := proc(code::mform, var) local doAdd;
        # TODO need to add support for loops and other structures
        doAdd := proc(c) local t, cs, f, h, flat;
	        h := Header(c);
	        if h = MStatSeq then
	            flat := M:-FlattenStatSeq(c);
	            if flat = MStatSeq() then
	                return MStatSeq();
	            end if;
	            MStatSeq(Front(flat), procname(Last(flat)));

	        elif h = MIfThenElse then
	            MIfThenElse(Cond(c), procname(Then(c)), procname(Else(c)));

	        elif h = MAssign then # shouldn't need this
	            MStatSeq(c, MAssign(var, op(1, c)));

	        elif h = MStandaloneExpr then
	            MAssign(var, op(c));

	        elif h = MStandaloneFunction then
	            MAssignToFunction(var, MFunction(op(c)));
	            
            elif typematch(c, MTry('t'::anything, 'cs'::anything, 'f'::anything)) then
                MTry(procname(t), procname(cs), MFinally(procname(op(f))));

            elif typematch(c, MTry('t'::anything, 'cs'::anything)) then
                MTry(procname(t), procname(cs));

            elif h = MCatchSeq then
                map(mc -> MCatch(CatchString(mc), doAdd(CatchBody(mc))), c);

            elif h = MError then
                c;
	        else
	            error "addAssigns, not supported yet: %1", h;
	        end if;
        end proc;

        return doAdd(code);
    end proc;


end module;
