
# Simple online partial evaluator for a subset of maple
# Only works on simple expressions


OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    export pe, pe_if;
    local EnvStack, genVar, genNum, code, makeGenerator;


##################################################################################

# Section: bunch of utility functions (may be moved into separate modules or files)

# returns a closure that generates unique names (as strings);
makeNameGenerator := proc(n::string) 
    local val;
    val := 0;
    return proc()
        val := val + 1;
        cat(n, val);
    end proc;
end proc;       

tagName := proc(tag, f)
    () -> tag(f())
end proc;


# for extracting subexpressions from inert procedures
getParams   := proc(x) option inline; op(1,x) end proc;
getLocals   := proc(x) option inline; op(2,x) end proc;
getProcBody := proc(x) option inline; op(5,x) end proc;

# for extracting subexpressions from inert statments
getHeader := proc(x) option inline; op(0,x) end proc;
getVal := proc(x) option inline; op(1,x) end proc;
getParamName := proc(x) `if`(op(0,x)=_Inert_DCOLON, op(op(1,x)), op(x)) end proc;

isExpDynamic := EvalExp:-isInert;
isExpStatic  := `not` @ isExpDynamic;

##################################################################################


# replaces params and local indices with their names
replace := proc(xs, f)
    i -> (f @ getParamName @ op)(i, xs);
end proc;

# returns a closure that maps param names to their indices
paramMap := proc(params, f)
    local tbl, i, c;
    tbl := table();
    c := 1;
    for i in params do
        tbl[getParamName(i)] := c;
        c := c + 1;
    end do;

    return x -> f(tbl[x]);
end proc;


# returns two closures used to generate locals in the postprocess
localMap := proc()
    local tbl, rep, c, newLocals;
    tbl := table();
    c := 1;

    rep := proc(x)
        if not assigned(tbl[x]) then
            tbl[x] := c;
            c := c + 1;
        end if;        
        _Inert_LOCAL(tbl[x]);
    end proc;

    newLocals := proc()
        _Inert_LOCALSEQ(op(map(x -> _Inert_NAME(lhs(x)), op(eval(tbl)))));
    end proc;

    return rep, newLocals;
end proc;



# takes an environment and an inert param
# returns the type expression of a function parameter type assertion
evalParamType := proc(env, param)
    if op(0, param) = _Inert_DCOLON then
        name := op(op(1, param));
        typ  := FromInert(op(2, param));

        if env:-fullyStatic?(name) then
            if not type(env:-getVal(name), eval(typ)) then
                error("Type assertion falure");
            end if;
        else
            env:-addType(name, typ);
        end if;
    end if;
end proc;


# if the argument is a procedure it is applied with no arguments
applythunk := proc(p)
    if type(p, procedure) then apply(p) end if;
end proc;


combineEnvs := proc(stack)
    local x;
    x := stack:-pop();
    while not stack:-empty() do
        x := x:-combine(stack:-pop());
    end do;
    x;
end proc;


#############################################################################


# called with a procedure, name of residual proc, and a list of equations
pe := proc(p::procedure, n::string, statlist::list(anything=anything))

    # set up globals
    genVar := makeNameGenerator("x");
    genNum := makeNameGenerator("");

    code := table();

    #create initial environment
    env := OnENV:-NewOnENV();
    for eqn in statlist do
        env:-addVal(lhs(eqn),rhs(eqn));
    end do;

    EnvStack := SimpleStack();
    EnvStack:-push(env);

    # get the inert form of the procedure
    inert := ToInert(eval(p));

    # specialize
    pe_specialize_proc(inert, n);

    EnvStack := 'EnvStack';

    # build a module from the global list of procs and return that

    return build_module(n);
    #return eval(code);
end proc;


# partially evalutates a statement sequence
pe_statseq := proc(statseq)
    subs_list := [_Inert_ASSIGN = pe_assign, _Inert_IF = pe_if, _Inert_RETURN = pe_return];
    eval(statseq, subs_list);
end proc;



# takes inert code and assumes static variables are on top of EnvStack
pe_specialize_proc := proc(inert, n::string)
    env := EnvStack:-top();
    params := getParams(inert);
    locals := getLocals(inert);
    body   := getProcBody(inert);

    #PRE-PROCESS, replace variable indices with names
    body := eval(body, [_Inert_PARAM = replace(params, _Inert_PARAM),
                        _Inert_LOCAL = replace(locals, _Inert_LOCAL)]);

    map( curry(evalParamType, env), params );

    # PARTIAL EVALUATION
    body := pe_statseq(body);

    # POST-PROCESS
    newParamList := select((env:-dynamic? @ getParamName), params);
    paramReplace := paramMap(newParamList, _Inert_PARAM);
    localReplace, newLocals := localMap();

    body := eval(body, [_Inert_PARAM = paramReplace, _Inert_LOCAL = localReplace]);
    
    newLocalList := newLocals();

    # create a name for the new procedure and add it to the global list

    code[n] := subsop(1=newParamList, 2=newLocalList, 5=body, inert);
end proc; 



# a function call
# assumes nested function calls have already been stripped out of the argument expressions
pe_function := proc(n)
    # get the code for the actual function from the interpreter
    inert := (ToInert @ eval @ convert)(op(1, n), name);
    if getHeader(inert) = _Inert_NAME then
        error("only defined functions are supported");
    end if;
    params := getParams(inert);

    env := OnENV:-NewOnENV();

    i := 0;
    processArg := proc(argExp)
        i := i + 1;
        reduced := EvalExp:-reduce(argExp, EnvStack:-top());
        if isExpStatic(reduced) then
            env:-putVal(op(op(i, params)), reduced);
            NULL;
        else
            reduced;
        end if;
    end proc;

    # reduce the argument expressions, these expressions should not be side effecting
    newArgs := map(processArg, args[2..-1]);
    
    #build a new environment for the function

    EnvStack:-push(env);
    newName := cat(op(1,n), "_", genNum());
    pe_specialize_proc(inert, newName); 
    EnvStack:-pop();    

    # residualize call
    _Inert_FUNCTION(_Inert_NAME(newName), newArgs);
end proc;


# partial evalutation of a single assignment statement
pe_assign := proc(name, expr)
    local assigns, stripped, reduced, inertAssigns;

    env := EnvStack:-top();
    inertAssigns, reduced := pe_expression(expr, env);

    if isExpStatic(reduced) then
        env:-putVal(name, reduced);
        _Inert_STATSEQ(op(inertAssigns));
    else
       _Inert_STATSEQ(op(inertAssigns), _Inert_ASSIGN(name, reduced));
    end if;    
end proc;


# pe for returns, all returns residualized for now
pe_return := proc(expr)
    inertAssigns, reduced := pe_expression(expr, EnvStack:-top());
    reduced := `if`(isExpStatic(reduced), ToInert(reduced), reduced);
    _Inert_STATSEQ(op(inertAssigns), _Inert_RETURN(reduced));    
end proc;


# takes an entire inert expression, including the header
pe_expression := proc(expr, env)
    #the expression stripper returns assigments as a list of equations
    assigns, strippedExpr := StripExp:-strip(expr, genVar);
    inertAssigns := pe_stripped_assigns(assigns);
    reduced := EvalExp:-reduce(strippedExpr, env);
    return inertAssigns, reduced;    
end proc;


# partial evaluation for the equations returned but the expression splitter
pe_stripped_assigns := proc(assigns::list(anything=anything))
    # resaidualize all function calls for now
    # process the inertAssigns (which are all function calls)
    inertAssigns := map(x -> _Inert_ASSIGN(_Inert_LOCAL(lhs(x)), rhs(x)), assigns);
    eval(inertAssigns, _Inert_FUNCTION = pe_function);    
end proc;


# in progress
pe_if := proc()
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

    pe_ifbranch := proc(ifbranch)
        if finished then return NULL end if;
        EnvStack:-push(EnvStack:-top():-clone());
      
        if getHeader(ifbranch) = _Inert_CONDPAIR then
            inertAssigns, reduced := pe_expression(op(1, ifbranch), EnvStack:-top());

            if isExpDynamic(reduced) then
                ifbody := pe_statseq(op(2, ifbranch));
                ifpart := _Inert_IF(_Inert_CONDPAIR(reduced, ifbody), 
                                    `if`(hasNextArg(), pe_ifbranch(nextArg()), NULL));
                res := _Inert_STATSEQ(op(inertAssigns), ifpart);
            elif reduced then
                ifbody := pe_statseq(op(2, ifbranch));
                finished := true;
                res := _Inert_STATSEQ(op(inertAssigns), ifbody);
            else
                res := _Inert_STATSEQ(op(inertAssigns));
            end if;
               
        else
            ifbody := pe_statseq(ifbranch);
            res := ifbody;
        end if;
  
        envColl:-push(EnvStack:-pop());        
        res;
    end proc;

    newif := pe_ifbranch(nextArg());

    newenv := combineEnvs(envColl);
    EnvStack:-pop();
    EnvStack:-push(newenv);
    return newif;
end proc;


########################################################################################


#builds a modle definition that contains the residual code
build_module := proc(n)
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
        
        processLocal := proc(localName)
            if localName = n then
                localIndex := nops(lexicalLocals) + 1;
            else
                if not member(localName, locals, localIndex) then
                    error(cat(localName, " is not a module local"));
                end if;                
            end if;
            
            if member(localName=localIndex, lexicalLocals, lexicalIndex) then
                _Inert_LEXICAL_LOCAL(lexicalIndex);
            else
                lexicalLocals := [op(lexicalLocals), localName=localIndex];
                _Inert_LEXICAL_LOCAL(nops(lexicalLocals));
            end if;
            
        end proc;
        
        
        body := eval(getProcBody(p), _Inert_NAME = processLocal);        
        
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



p1 := proc(x, y)
    local z;
    z := x + y;
    return z;
end proc;


p2 := proc(x, y)
    local z;
    z := x + p1(x, y) + 10;
    return z;
end proc;


p3 := proc(x, y::integer)
    local z;
    z := x + y;
    return z;
end proc;


p4 := proc(x, y, z)
    if x = y then
        return z;
    end if;
    return z;
end proc;

p5 := proc(x, y, z)
    if x = y then
        return x;
    elif p1(x,y) > 10 then
        return y;
    else
        return z;
    end if;
end proc;


