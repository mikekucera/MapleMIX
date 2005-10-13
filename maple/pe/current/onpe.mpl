# Simple online partial evaluator for a subset of maple

OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    local EnvStack, code, genVar, genNum;
    export PartiallyEvaluate;

##################################################################################


getStaticValue := proc(m::m)
    res := M:-ReduceExp(m, OnENV:-NewOnENV());
    `if`(M:-IsM(res), FAIL, res);
end proc;

isStaticValue := proc(m::m)
    evalb(getStaticValue(m) <> FAIL);
end proc;


##################################################################################


# takes an environment and an inert param
# returns the type expression of a function parameter type assertion
#evalParamType := proc(env, param)
#    if op(0, param) = _Inert_DCOLON then
#        name := op(op(1, param));
#        typ  := FromInert(op(2, param));
#
#        if env:-fullyStatic?(name) then
#            if not type(env:-getVal(name), eval(typ)) then
#                error("Type assertion falure");
#            end if;
#        else
#            env:-addType(name, typ);
#        end if;
#    end if;
#end proc;


growEnvStack := proc()
    EnvStack:-push(EnvStack:-top():-clone());
end proc;


############################################################################
# The specializer
############################################################################


# called with a procedure, name of residual proc, and a list of equations
# sets up the partial evaluation
PartiallyEvaluate := proc(p::procedure, vallist::list(`=`) := [])
    # set up globals
    genVar := NameGenerator:-New("x");
    genNum := NameGenerator:-New("");
    code := table();

    #create initial environment
    env := OnENV:-NewOnENV();
    for eqn in vallist do
        env:-putVal(lhs(eqn),rhs(eqn));
    end do;

    EnvStack := SimpleStack();
    EnvStack:-push(env);

    # get the m form of the procedure
    m := M:-ToM(p);

    # specialize
    use procName = "ModuleApply" in
        peSpecializeProc(m, procName);
        EnvStack := 'EnvStack';
        # build a module from the global list of procs and return that
        return build_module(procName);
        
        #return copy(code);
    end use;
end proc;



# takes inert code and assumes static variables are on top of EnvStack
peSpecializeProc := proc(m::m, n::string) #void
    env := EnvStack:-top();

    params := M:-Params(m);
    body   := M:-ProcBody(m);

    # should be able to store the actual type in the M form
    # eg MDcolon(MName("x"), MType(integer)); that way below line is not needed    
    #map( curry(evalParamType, env), params );

    # PARTIAL EVALUATION
    body := M:-TransformIfNormalForm(body);
    body := M:-AddImplicitReturns(body);
    body := peInert(body);
    #body := M:-TransformIfNormalForm(body);

    # POST-PROCESS
    #leftoverParams := {};
    #leftoverParam := proc(n)
    #    leftoverParams := {op(leftoverParams), n};
    #end proc;
    #eval(body, MParam=leftoverParam);

    newParamList := select(x -> env:-isDynamic(op(1,x)), params);        
    code[n] := subsop(1=newParamList, 5=body, m);
end proc; 


# Given an inert procedure and an inert function call to that procedure, decide if unfolding should be performed.
isUnfoldable := proc(inertFunctionCall::m(Function), inertProcedure::m(Proc))
    return true;
    #if nops(op(2, inertFunctionCall)) = 0 then # all the arguments were static and reduced away
    #   return true;
    #else
    #   flattened := flattenStatseq(getProcBody(inertProcedure));
    #   return evalb( nops(flattened) = 1 and op([1,0], flattened) = _Inert_RETURN and isStaticValue(op([1,1], flattened)) );
    #end if;
    #false;        
end proc;


# partially evaluates an arbitrary M code
peInert := proc(m::m) # returns inert code or NULL
    local header;
    header := M:-Header(m);
    if assigned(pe[header]) then
        return pe[header](op(m));
    end if;
    error cat("not supported yet: ", header);
end proc;


# pe for an expression that is to be residualized
peResidualizeExpr := proc(k, m::m)
    res := M:-ReduceExp(m, EnvStack:-top());
	k(`if`(M:-IsM(res), res, M:-ToM(res)));
end proc;

pe[MStandaloneExpr] := curry(peResidualizeExpr, MStandaloneExpr);
pe[MReturn] := curry(peResidualizeExpr, MReturn);


pe[MStatSeq] := proc()
    q := SimpleQueue();
    for i from 1 to nargs do
        res := peInert([args][i]);
        if nops([res]) > 0 then
            q:-enqueue(res);
            if M:-EndsWithReturn(res) then 
                break 
            end if;
        end if;
    end do;
    MStatSeq(op(q:-toList()));
end proc;


pe[MIfThenElse] := proc(cond, s1, s2)
    print("cond", cond);
    reduced := M:-ReduceExp(cond, EnvStack:-top());
    print("reduced", reduced);
    if M:-IsM(reduced) then
        growEnvStack();
        reds1 := peInert(s1);
        thenEnv := EnvStack:-pop();
        growEnvStack();
        reds2 := peInert(s2);
        elseEnv := EnvStack:-pop();
        EnvStack:-pop();
        EnvStack:-push(thenEnv:-combine(elseEnv));
        
        # if reds1 and reds2 are both empty then its a no-op
        if reds1 = MStatSeq() and reds2 = MStatSeq() then
            MStatSeq();
        else
            MIfThenElse(reduced, reds1, reds2);
        end if;
    else
        peInert(`if`(reduced, s1, s2))
    end if;
end proc;


pe[MAssign] := proc(n::m(Local), expr::m)
	env := EnvStack:-top();
    reduced := M:-ReduceExp(expr, env);
    if M:-IsM(reduced) then
        MAssign(n, reduced);
    else
        env:-putVal(op(n), reduced);
        NULL;
    end if;
end proc;



pe[MStandaloneFunction] := proc(n::m(AssignedName))
    residualFunctionCall := peFunction(args);
    funcName := op([1,1], residualFunctionCall);
    residualProcedure := code[funcName];

    if isUnfoldable(residualFunctionCall, residualProcedure) then
        code[funcName] := evaln(code[funcName]); # remove mapping from code        
        M:-Unfold:-UnfoldStandalone(residualProcedure, residualFunctionCall, genVar);
    else
        residualFunctionCall;
    end if;
end proc;



pe[MAssignToFunction] := proc(var::m(SingleUse), funcCall::m(Function))
    varName := op(var);
    residualFunctionCall := peFunction(op(funcCall));
    
    funcName := op([1,1], residualFunctionCall);
    residualProcedure := code[funcName];
        
    if isUnfoldable(residualFunctionCall, residualProcedure) then
        code[funcName] := evaln(code[funcName]); # remove mapping from code        
        # transform the body of the proc, prepare it for unfolding
        res := M:-Unfold:-UnfoldIntoAssign(residualProcedure, residualFunctionCall, genVar, var);
        flattened := M:-FlattenStatSeq(res);

        # If resulting statseq has only one statment
        # It must be an assign because thats what UnfoldIntoAssign does
        if nops(flattened) = 1 then            
            assign := op(flattened);
            expr := op(2, assign);
            val := getStaticValue(expr);
            if val <> FAIL then
                varName := op([1,1], assign);
                EnvStack:-top():-putVal(varName, val);                
                return;            
            end if;
        end if;
        flattened;
    else
        MAssign(var, residualFunctionCall);
    end if;
end proc;



# Assumes nested function calls have already been stripped out of the argument expressions.
# Always returns a function call, code for specialized function will be in the 'code' module variable.
peFunction := proc(n::m({AssignedName,Name}), argExpSeq::m(ExpSeq)) ::m(Function);
    # get the code for the actual function from the underlying interpreter
    m := M:-ToM(convert(op(1,n), name));    
    if M:-Header(m) = MName then
        error("only defined functions are supported");
    end if;

    params := M:-Params(m);
    top := EnvStack:-top();
    
    # new environment for called function, will contain static arg values
    env := OnENV:-NewOnENV();

    i := 0;
    processArg := proc(argExp)
        i := i + 1;
        reduced := M:-ReduceExp(argExp, top);
        if not M:-IsM(reduced) then
            # put static argument value into environment
            env:-putVal(op(op(i, params)), reduced);
            NULL;
        # TODO this needs to work with any expressions, not just single variables
        #elif isInertVariable(reduced) and top:-hasTypeInfo?(getVal(reduced)) then
        #     env:-addTypeSet(getVal(reduced), top:-getTypes(getVal(reduced)));
        #     reduced;
        else
            reduced;
        end if;
    end proc;
 
    # reduce the argument expressions, these expressions should not be side effecting
    newArgs := map(processArg, argExpSeq);
    
    #build a new environment for the function
    EnvStack:-push(env);
    newName := cat(op(1,n), "_", genNum());
    peSpecializeProc(m, newName); 
    EnvStack:-pop();    

    # return residualized function call
    MFunction(MName(newName), newArgs);
end proc;




########################################################################################


#builds a modle definition that contains the residual code
build_module := proc(n::string)::inert;
    # get a list of names of module locals
    locals := remove(x -> evalb(x=n), ListTools:-Flatten([indices(code)]));
  
    # each non exported proc will need a local index
    procLocalIndex := 0;

    # will be mapped over each residualized procedure
    processProc := proc(eqn)
        procName, p := lhs(eqn), M:-FromM(rhs(eqn));
        
        procLocalIndex := procLocalIndex + `if`(procName = n, 0, 1);
        
        lexicalLocals := []; #list of lexical pairs(equations) of local name to index

        # used to evaluate each name reference
        
        processFuncCall := proc(n)
            if M:-Header(n) = _Inert_ASSIGNEDNAME then
                return _Inert_FUNCTION(args);
            end if;

            localName := op(1, n); # strip off the _Inert_NAME
            if localName = n then
                localIndex := nops(lexicalLocals) + 1;
            else
                if not member(localName, locals, localIndex) then
                    return _Inert_FUNCTION(args); #error(cat("'", localName, "' is not a module local"));
                end if;                
            end if;
            
            if member(localName=localIndex, lexicalLocals, lexicalIndex) then
                subsop(1=_Inert_LEXICAL_LOCAL(lexicalIndex), _Inert_FUNCTION(args));
            else
                lexicalLocals := [op(lexicalLocals), localName=localIndex];
                subsop(1=_Inert_LEXICAL_LOCAL(nops(lexicalLocals)), _Inert_FUNCTION(args));
            end if;
            
        end proc;
        
        
        body := eval(M:-ProcBody(p), _Inert_FUNCTION = processFuncCall);        
        
        f := proc(e)
            _Inert_LEXICALPAIR(_Inert_NAME(lhs(e)),_Inert_LOCAL(rhs(e)));
        end proc;

        seq := map(f, lexicalLocals);
        
        lexicalLocals := _Inert_LEXICALSEQ( op(seq) );
        p := subsop(5=body, 8=lexicalLocals, p);
        
        _Inert_ASSIGN(_Inert_LOCAL( `if`(procName = n, nops(locals) + 1, procLocalIndex) ) ,p);
    end proc;

    moduleStatseq := _Inert_STATSEQ(op(map(processProc, op(op(code)))));
    locals := _Inert_LOCALSEQ(op(map(_Inert_NAME, [op(locals)])));
    exports := _Inert_EXPORTSEQ(_Inert_NAME(n));
    
    # get a bare bones inert module then substitute
    inertModDef := ToInert('module() end module');
    subsop(2 = locals, 4 = exports, 5 = moduleStatseq, inertModDef);
end proc;

end module: