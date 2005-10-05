# Simple online partial evaluator for a subset of maple

OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
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


combineEnvs := proc(stack)
    local x;
    x := stack:-pop();
    while not stack:-empty() do
        x := x:-combine(stack:-pop());
    end do;
    x;
end proc;




############################################################################
# The specializer
############################################################################


# called with a procedure, name of residual proc, and a list of equations
# sets up the partial evaluation
PartiallyEvaluate := proc(p::procedure, vallist::list(`=`) := [])
    # set up globals
    genVar := makeNameGenerator("x");
    genNum := makeNameGenerator("");
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
        #return build_module(procName);
        
        return op(code);
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
    #body := TransformIfNormalForm(body);
    body := peInert(body);
    #body := TransformIfNormalForm(body);

    # POST-PROCESS
    leftoverParams := {};
    leftoverParam := proc(n)
        leftoverParams := {op(leftoverParams), n};
    end proc;
    eval(body, _Inert_PARAM=leftoverParam);

    newParamList := select(x -> member(leftoverParams, op(1,x)), params);

    code[n] := subsop(1=newParamList, 5=body, inert);
end proc; 



# partially evaluates an arbitrary inert code
peInert := proc(inert::Or(inert, tag)) # returns inert code or NULL
   local header;
   header := getHeader(inert);
   if assigned(pe[header]) then
        pe[header](op(inert));
   else
        error(cat("not supported yet: ", op(0, inert)));
   end if;
end proc;



# returns two values because pe[_Tag_STRIPPED] returns two values
peExpression := proc(expr::inert)
    a, b := StripExp:-strip(expr, genVar);
    peInert(a), peInert(b);
end proc;



#pe[_Tag_STRIPPED] := proc(assigns::tag(STRIPPEDASSIGNSEQ), expr::tag(STRIPPEDEXPR))
#    q := SimpleQueue();
#    #subsList := [];
#        
#    for i from 1 to nops(assigns) do
#        #res := subs(subsList, op(i, assigns));                      
#        res := peInert(res);
#        
#        if nops([res]) = 1 then # if residual code consists of a single statment then it must be an assign to an expression
#            subsList := [op(subsList), op([1,1], res) = op([1,2], res)];
#        elif nops([res]) > 1 then
#            q:-enqueue(res);
#            if endsWithReturn(res) then break end if;
#        end if;    
#    end do;
#    
#    _Inert_STATSEQ(op(q:-toList())), peInert(subs(subsList, expr));
#end proc;


pe[_Tag_STRIPPEDEXPR] := proc(expr::inert)
    EvalExp:-reduce(expr, EnvStack:-top());
end proc;


# pe for returns, all returns residualized for now
pe[_Inert_RETURN] := proc(expr::inert)
    inertAssigns, reduced := peExpression(expr);
    reduced := `if`(isInert(reduced), reduced, ToInert(reduced));
    _Inert_STATSEQ(op(inertAssigns), _Inert_RETURN(reduced));
end proc;


# partial evaluation of an expression that is not part of a statment, usually an implicit return
peStandaloneExpression := proc(inertForm)
    return proc()
        inertAssigns, reduced := peExpression(inertForm(args));
        reduced := `if`(isInert(reduced), reduced, ToInert(reduced));
        _Inert_STATSEQ(op(inertAssigns), reduced);
    end proc;
end proc;

for inertForm in expressionForms do
    pe[inertForm] := peStandaloneExpression(inertForm);
end do;


# map over statement sequences
pe[_Inert_STATSEQ] := proc()
    q := SimpleQueue();
    for i from 1 to nops([args]) do
        res := peInert([args][i]);
        if nops([res]) > 0 then
            q:-enqueue(res);
            if endsWithReturn(res) then break end if;
        end if;
    end do;
    _Inert_STATSEQ(op(q:-toList()));
end proc;




# Given an inert procedure and an inert function call to that procedure, decide if unfolding should be performed.

isUnfoldable := proc(inertFunctionCall::inert(FUNCTION), inertProcedure::inert(PROC))
    return true;
    if nops(op(2, inertFunctionCall)) = 0 then # all the arguments were static and reduced away
       return true;
    else
       flattened := flattenStatseq(getProcBody(inertProcedure));
       return evalb( nops(flattened) = 1 and op([1,0], flattened) = _Inert_RETURN and isStaticValue(op([1,1], flattened)) );
    end if;
    false;        
end proc;




# Assumes nested function calls have already been stripped out of the argument expressions.
# Always returns a function call, code for specialized function will be in the 'code' module variable.
peFunction := proc(n::inert({ASSIGNEDNAME,NAME}))::inert(FUNCTION);
    # get the code for the actual function from the underlying interpreter
    inert := (ToInert @ eval @ convert)(getVal(n), name);

    if getHeader(inert) = _Inert_NAME then
        error("only defined functions are supported");
    end if;

    params := getParams(inert);

    top := EnvStack:-top();
    # new environment for called function, will contain static arg values
    env := OnENV:-NewOnENV();

    i := 0;
    processArg := proc(argExp)
        i := i + 1;
        reduced := EvalExp:-reduce(argExp, EnvStack:-top());
        if not isInert(reduced) then
            # put static argument value into environment
            env:-putVal(op(op(i, params)), reduced);
            NULL;
        # TODO this needs to work with any expressions, not just single variables
        elif isInertVariable(reduced) and top:-hasTypeInfo?(getVal(reduced)) then
            env:-addTypeSet(getVal(reduced), top:-getTypes(getVal(reduced)));
            reduced;
        else
            reduced;
        end if;
    end proc;

    # reduce the argument expressions, these expressions should not be side effecting
    newArgs := map(processArg, args[2..-1]);
    
    #build a new environment for the function

    EnvStack:-push(env);
    newName := cat(op(1,n), "_", genNum());
    peSpecializeProc(inert, newName); 
    EnvStack:-pop();    

    # residualize call
    # this is where decision to unfold would likely go
    _Inert_FUNCTION(_Inert_NAME(newName), newArgs);
end proc;



# only works for a standalone function
# this should override previous pe table assignment that treats a function as an expression
pe[_Inert_FUNCTION] := proc(n::inert(ASSIGNEDNAME))
    residualFunctionCall := peFunction(args);
    funcName := op([1,1], residualFunctionCall);
    residualProcedure := code[funcName];

    if isUnfoldable(residualFunctionCall, residualProcedure) then
        code[funcName] := evaln(code[funcName]); # remove mapping from code        
        TransformUnfold:-UnfoldStandalone(residualProcedure, residualFunctionCall, genVar);
    else
        residualFunctionCall;
    end if;
end proc;


# an assign that has as its expression a single function call 
pe[_Tag_ASSIGNTOFUNCTION] := proc(var::inert(LOCAL), funcCall::inert(FUNCTION))
    varName := op(var);
    residualFunctionCall := peFunction(op(funcCall));
    
    funcName := op([1,1], residualFunctionCall);
    residualProcedure := code[funcName];
        
    if isUnfoldable(residualFunctionCall, residualProcedure) then
        code[funcName] := evaln(code[funcName]); # remove mapping from code        
        # transform the body of the proc, prepare it for unfolding
        res := TransformUnfold:-UnfoldIntoAssign(residualProcedure, residualFunctionCall, genVar, op(varName));
        flattened := flattenStatseq(res);

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
        _Inert_ASSIGN(_Inert_LOCAL(varName), residualFunctionCall);
    end if;
end proc;




# partial evalutation of a single assignment statement
pe[_Inert_ASSIGN] := proc(name::inert(LOCAL), expr::inert)
    # TODO, inertAssigns a bad name because function may have been unfolded
    inertAssigns, reduced := peExpression(expr);
    if isInert(reduced) then
        #if getHeader(op(-1, inertAssigns)) <> _Inert_STATSEQ then error("must return a statment sequence") end if;        
        #lastStat := op([-1, -1], inertAssigns);        

        #if isInertVariable(reduced) 
        #and op(0, lastStat) = _Inert_ASSIGN     
        #and getVal(reduced) = op([1,1], lastStat) then                       
        #    _Inert_STATSEQ(op(1..-2, inertAssigns), op([-1, 1..-2], inertAssigns), _Inert_ASSIGN(name, op(2, lastStat)));            
        #else
            _Inert_STATSEQ(op(inertAssigns), _Inert_ASSIGN(name, reduced));
        #end if;
    else
        EnvStack:-top():-putVal(op(name), reduced);
        _Inert_STATSEQ(op(inertAssigns)); # TODO, is it possible for an expression to reduce to some assigns AND a static value?
    end if;
end proc;




pe[_Inert_IF] := proc()
    envColl := SimpleStack();    
    finished := false;
    outerArgs := args;
    # proc that will return outer arguments in sequence
    
    # the following code I want to pull out into its own module
    currentArg := 1;
    nextArg := proc()
        if not hasNextArg() then return NULL end if;
        res := [outerArgs][currentArg];
        currentArg := currentArg + 1;
        res;
    end proc;
    hasNextArg := () -> evalb(currentArg <= nops([outerArgs]));    

    #env := EnvStack:-top();

    peIfBranch := proc(ifbranch)
        if finished then return NULL end if;
        EnvStack:-push(EnvStack:-top():-clone());
      
        if getHeader(ifbranch) = _Inert_CONDPAIR then
            inertAssigns, reduced := peExpression(op(1, ifbranch));
            if isInert(reduced) then
                ifbody := peInert(op(2, ifbranch));
                ifpart := _Inert_IF(_Inert_CONDPAIR(reduced, ifbody), 
                                    `if`(hasNextArg(), peIfBranch(nextArg()), NULL));
                res := _Inert_STATSEQ(op(inertAssigns), ifpart);
            elif reduced then
                ifbody := peInert(op(2, ifbranch));
                finished := true;
                res := _Inert_STATSEQ(op(inertAssigns), ifbody);
            else
                # assigns must be preserved because they might be side effecting
                res := _Inert_STATSEQ(op(inertAssigns), peIfBranch(nextArg(), NULL));
            end if;               
        else
            ifbody := peInert(ifbranch);
            res := ifbody;
        end if;
  
        envColl:-push(EnvStack:-pop());        
        res;
    end proc;

    newif := peIfBranch(nextArg());

    newenv := combineEnvs(envColl);
    EnvStack:-pop();
    EnvStack:-push(newenv);
    return newif;
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
        procName, p := lhs(eqn), rhs(eqn);
        
        procLocalIndex := procLocalIndex + `if`(procName = n, 0, 1);
        
        lexicalLocals := []; #list of lexical pairs(equations) of local name to index

        # used to evaluate each name reference
        
        processFuncCall := proc(n)
            if getHeader(n) = _Inert_ASSIGNEDNAME then
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
        
        
        body := eval(getProcBody(p), _Inert_FUNCTION = processFuncCall);        
        
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


end module;


######################################################################################
