
# Simple online partial evaluator for a subset of maple
# Only works on simple expressions


OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    export pe, makeGenerator;
    local EnvStack, genVar, genNum, code;


##################################################################################


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

isExpDynamic := x -> EvalExp:-isInert(x);
isExpStatic  := x -> not isExpDynamic(x);


subs_list := [
    _Inert_ASSIGN = pe_assign
];


# replaces params and local indices with their names
replace := proc(xs, f)
    i -> f(op(op(i, xs)));
end proc;

# returns a closure that maps param names to their indices
paramMap := proc(params, f)
    local tbl, i, c;
    tbl := table();
    c := 1;
    for i in params do
        tbl[op(i)] := c;
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



# takes inert code and assumes static variables are on top of EnvStack
pe_specialize_proc := proc(inert, n::string)
    env := EnvStack:-top();
    params := getParams(inert);
    locals := getLocals(inert);
    body   := getProcBody(inert);

    #PRE-PROCESS, replace variable indices with names
    body := eval(body, [_Inert_PARAM = replace(params, _Inert_PARAM),
                        _Inert_LOCAL = replace(locals, _Inert_LOCAL)]);

    # PARTIAL EVALUATION
    body := eval(body, subs_list);

    # POST-PROCESS
    newParamList := select((env:-dynamic? @ getVal), params);
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


pe_assign := proc(name, expr)
    local assigns, stripped, reduced, inertAssigns;
    assigns, stripped := StripExp:-strip(expr, genVar);
    
    # residualize all function calls for now
    # process the inertAssigns (which are all function calls)
    inertAssigns := map(x -> _Inert_ASSIGN(_Inert_LOCAL(lhs(x)), rhs(x)), assigns);

    inertAssigns := eval(inertAssigns, _Inert_FUNCTION = pe_function);    

    reduced := EvalExp:-reduce(stripped, EnvStack:-top());
    if isExpStatic(reduced) then
        env:-putVal(name, reduced);
        _Inert_STATSEQ(op(inertAssigns));
    else
       _Inert_STATSEQ(op(inertAssigns), _Inert_ASSIGN(name, reduced));
    end if;    
end proc;


#builds a modle definition that contains the residual code
build_module := proc(n)
    
    # get a list of names of module locals
    locals := remove(x -> evalb(x=n), ListTools:-Flatten([indices(code)]));

    i := 0;
    # will be mapped over each residualized procedure
    processProc := proc(eqn)
        procName = lhs(eqn);
        
        i := `if`(procName = n, i, i + 1);
        
        lexicalLocals := []; #list of lexical pairs(equations) of local name to index

        # used to evaluate each name reference
        
        processLocal := proc(localName)
            if localName = n then
                localIndex := nops(lexicalLocals) + 1;
            else
                member(localName, locals, localIndex);
            end if;
            
            if member(localName=localIndex, lexicalLocals, lexicalIndex) then
                _Inert_LEXICAL_LOCAL(lexicalIndex);
            else
                lexicalLocals := [op(lexicalLocals), localName=localIndex];
                _Inert_LEXICAL_LOCAL(nops(lexicalLocals));
            end if;
            
        end proc;
        
        p := rhs(eqn);
        body := eval(getProcBody(p), _Inert_NAME = processLocal);
        
        
        f := proc(e)
            _Inert_LEXICALPAIR(_Inert_NAME(lhs(e)),_Inert_LOCAL(rhs(e)));
        end proc;

        seq := map(f, lexicalLocals);
        
        lexicalLocals := _Inert_LEXICALSEQ( op(seq) );
        p := subsop(5=body, 8=lexicalLocals, p);
        
        _Inert_ASSIGN(_Inert_LOCAL( `if`(procName = n, nops(locals) + 1, i) ) ,p);
    end proc;

    moduleStatseq := _Inert_STATSEQ(op(map(processProc, op(op(code)))));
    locals := _Inert_LOCALSEQ(map(_Inert_NAME, op(locals)));
    exports := _Inert_EXPORTSEQ(_Inert_NAME(n));
    
    # get a bare bones inert module then substitute
    inertModDef := ToInert('module() end module');
    inertModDef := subsop(2 = locals, 4 = exports, 5 = moduleStatseq, inertModDef);
    return inertModDef;    

end proc;


end module;




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