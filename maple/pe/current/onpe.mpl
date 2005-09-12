
read("types.mpl");
read("OnENV.mpl");
read("strip_exp.mpl");
read("eval_exp.mpl");


# Simple online partial evaluator for a subset of maple

OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    export PartiallyEvaluate;
    local EnvStack, genVar, genNum, code, makeGenerator;

#################################################################################

kernelopts(assertlevel=2);

##################################################################################

# Section: bunch of utility functions (may be moved into separate modules or files)

# returns a closure that generates unique names (as strings)
makeNameGenerator := proc(n::string)::procedure;
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


############################################################################


# called with a procedure, name of residual proc, and a list of equations
# sets up the partial evaluation
PartiallyEvaluate := proc(p::procedure, vallist::list(equation))#::moduledefinition;
    # set up globals
    genVar := makeNameGenerator("x");
    genNum := makeNameGenerator("");
    code := table();

    #create initial environment
    env := OnENV:-NewOnENV();
    for eqn in vallist do
        env:-addVal(lhs(eqn),rhs(eqn));
    end do;

    EnvStack := SimpleStack();
    EnvStack:-push(env);

    # get the inert form of the procedure
    inert := ToInert(eval(p));

    # specialize
    use procName = "ModuleApply" in
        peSpecializeProc(inert, procName);
        EnvStack := 'EnvStack';
        # build a module from the global list of procs and return that
        return build_module(procName);
        #return op(code);
    end use;
end proc;


# partially evaluates an arbitrary inert code
peInert := proc(inert::inert) # returns inert code or NULL
   local header;
   header := getHeader(inert);
   if assigned(pe[header]) then
        pe[header](op(inert));
   else
        error(cat("not supported yet: ", op(0, inert)));
   end if;
end proc;


# takes inert code and assumes static variables are on top of EnvStack
peSpecializeProc := proc(inert::inert, n::string) #void
    env := EnvStack:-top();
    params := getParams(inert);
    locals := getLocals(inert);
    body   := getProcBody(inert); #body must be a STATSEQ

    #PRE-PROCESS, replace variable indices with names
    body := eval(body, [_Inert_PARAM = replace(params, _Inert_PARAM),
                        _Inert_LOCAL = replace(locals, _Inert_LOCAL)]);

    map( curry(evalParamType, env), params );

    # PARTIAL EVALUATION
    body := peInert(body);

    # POST-PROCESS
    newParamList := select((env:-dynamic? @ getParamName), params);
    paramReplace := paramMap(newParamList, _Inert_PARAM);
    localReplace, newLocals := localMap();

    body := eval(body, [_Inert_PARAM = paramReplace, _Inert_LOCAL = localReplace]);
    
    newLocalList := newLocals();

    code[n] := subsop(1=newParamList, 2=newLocalList, 5=body, inert);
end proc; 


# takes an entire inert expression, including the header
peExpression := proc(expr::inert, env)
    #the expression stripper returns assigments as a list of equations
    assigns, strippedExpr := StripExp:-strip(expr, genVar);
    inertAssigns := map(eqn -> _Inert_ASSIGN(_Inert_LOCAL(lhs(eqn)), peInert(rhs(eqn))), assigns);
    reduced := EvalExp:-reduce(strippedExpr, env);
    return inertAssigns, reduced;    
end proc;


# map over statement sequences
pe[_Inert_STATSEQ] := proc()
    q := SimpleQueue();
    for i from 1 to nops([args]) do
        res := peInert([args][i]);
        q:-enqueue(res);

        # if a return is encountered then stop processing
        # may need a better solution in the future
        if getHeader(res) = _Inert_RETURN or
           (getHeader(res) = _Inert_STATSEQ and getHeader(op(nops(res),res)) = _Inert_RETURN) then
            break;
        end if;
    end do;
    _Inert_STATSEQ(op(q:-toList()));
end proc;


# assumes nested function calls have already been stripped out of the argument expressions
pe[_Inert_FUNCTION] := proc(n::inert(ASSIGNEDNAME))
    # get the code for the actual function from the interpreter
    inert := (ToInert @ eval @ convert)(op(1, n), name);
    if getHeader(inert) = _Inert_NAME then
        error("only defined functions are supported");
    end if;
    params := getParams(inert);

    # new environments for called function, will contain static arg values
    env := OnENV:-NewOnENV();

    i := 0;
    processArg := proc(argExp)
        i := i + 1;
        reduced := EvalExp:-reduce(argExp, EnvStack:-top());
        if isExpStatic(reduced) then
            # put static argument value into environment
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
    peSpecializeProc(inert, newName); 
    EnvStack:-pop();    

    # residualize call
    # this is where decision to unfold would likely go
    _Inert_FUNCTION(_Inert_NAME(newName), newArgs);
end proc;


# partial evalutation of a single assignment statement
pe[_Inert_ASSIGN] := proc(name::inert(LOCAL), expr::inert)
    env := EnvStack:-top();
    inertAssigns, reduced := peExpression(expr, env);

    if isExpStatic(reduced) then
        env:-putVal(name, reduced);
        _Inert_STATSEQ(op(inertAssigns));
    else
       _Inert_STATSEQ(op(inertAssigns), _Inert_ASSIGN(name, reduced));
    end if;    
end proc;


# pe for returns, all returns residualized for now
pe[_Inert_RETURN] := proc(expr::inert)
    inertAssigns, reduced := peExpression(expr, EnvStack:-top());
    reduced := `if`(isExpStatic(reduced), ToInert(reduced), reduced);
    _Inert_STATSEQ(op(inertAssigns), _Inert_RETURN(reduced));
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
            inertAssigns, reduced := peExpression(op(1, ifbranch), EnvStack:-top());

            if isExpDynamic(reduced) then
                ifbody := peInert(op(2, ifbranch));
                ifpart := _Inert_IF(_Inert_CONDPAIR(reduced, ifbody), 
                                    `if`(hasNextArg(), peIfBranch(nextArg()), NULL));
                res := _Inert_STATSEQ(op(inertAssigns), ifpart);
            elif reduced then
                ifbody := peInert(op(2, ifbranch));
                finished := true;
                res := _Inert_STATSEQ(op(inertAssigns), ifbody);
            else
                res := _Inert_STATSEQ(op(inertAssigns));
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
            print("what?", n);
            if getHeader(n) = _Inert_ASSIGNEDNAME then
                return _Inert_FUNCTION(args);
            end if;

            localName := op(1, n); # strip off the _Inert_NAME
            if localName = n then
                localIndex := nops(lexicalLocals) + 1;
            else
                if not member(localName, locals, localIndex) then
                    error(cat("'", localName, "' is not a module local"));
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




p6 := proc(x, y)
    if p1(x,y) > 10 then
        if p1(x, y) > 100 then
            return "greater than 100";
        else
            return "less than 100";
        end if;
    else
        return "no";
    end if;
end proc;


p7 := proc(x)
    return x;
    return x;
end proc;


p8 := proc(x::integer)
    if type(x, integer) then 
        return 1;
    end if;
    return 0;
end proc;
