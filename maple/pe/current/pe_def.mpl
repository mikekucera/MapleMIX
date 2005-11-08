# Simple online partial evaluator for a subset of maple

OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    local callStack, code, gen, mcache,
          CallStack;
    export ModuleApply, PartiallyEvaluate, OnENV, ReduceExp;

ModuleApply := PartiallyEvaluate;


$include "pe_stack.mpl"

$include "pe_onenv.mpl";

$include "pe_reduce_exp.mpl"
    
##################################################################################

# caches M code of procedures so don't need to call ToM unneccesarily
getMCode := proc(fun)
    if assigned(mcache[eval(fun)]) then
        mcache[eval(fun)];
    else
        mcache[eval(fun)] := M:-ToM(ToInert(eval(fun)));
    end;
end proc;

getStaticValue := proc(m::m)
    res := ReduceExp(m);
    `if`(M:-IsM(res), FAIL, res);
end proc;

isStaticValue := proc(m::m)
    evalb(getStaticValue(m) <> FAIL);
end proc;

# map all locals in the localseq to generated escaped locals
#mapLocalsToSymbols := proc(env, locals::m(LocalSeq))
#    for n in locals do
#        s := op(1,n);
#        env:-putVal(s, `tools/gensym`(s));
#    end do;
#    NULL
#end proc;


Header := proc(x) option inline; op(0,x) end proc;
# for dealing with closures
Lex  := proc(x) option inline; op(1,x) end proc;
Code := proc(x) option inline; op(2,x) end proc;


################################################################################



lift := proc(x)
    head := Header(x);
    if member(head, {MInt, MString, MParam, MName,
                     MLocal, MGeneratedName, MSingleUse, 
                     MAssignedName, MLocalName}) then
        x;
    elif head = Closure then
        Code(x);
    elif head = SModuleLocal then
        error "cannot lift a module local yet";
    elif head = SArgs then
        MArgs();
    elif M:-IsM(x) then
        map(procname, x);
    else
	    M:-ToM(ToInert(x));
	end if;
end proc;


# lifts all static values that are embedded in the residual code
# meant to be used as a post-process
liftCode := proc()
    for pn in map(op, [indices(code)]) do
        body := M:-ProcBody(code[pn]);
        code[pn] := subsop(5=lift(body), code[pn]);
    end do;
    NULL;
end proc;



################################################################################


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

############################################################################
# The specializer
############################################################################


# called with a procedure, name of residual proc, and a list of equations
# sets up the partial evaluation
PartiallyEvaluate := proc(p::procedure)
    # set up module locals
    gen := NameGenerator();
    callStack := CallStack();
    code := table();
    mcache := table();

    m := getMCode(p);
    
    newEnv := OnENV();
    newEnv:-setArgs(table());
    #mapLocalsToSymbols(newEnv, M:-Locals(m));
    callStack:-push(newEnv);

    # perform partial evaluation    
    peSpecializeProc(m, "ModuleApply");           
    liftCode();
    res :=  (eval @ FromInert @ build_module)("ModuleApply");
    #return copy(code);
    
    # unassign module locals
    gen := 'gen';
    callStack := 'callStack';
    code := 'code';
    mcache := 'mcache';        
    
    return res;
end proc;



# takes inert code and assumes static variables are on top of callStack
# called before unfold
peSpecializeProc := proc(m::m, n := "") #void    
    params := M:-Params(m);
    body   := M:-ProcBody(m);

    body := M:-TransformIfNormalForm(body);
    body := M:-AddImplicitReturns(body);
    
    body := peM(body); # Partial Evaluation
    
    newProc := subsop(5=body, m);    
    newProc := M:-SetArgsFlags(newProc);
    
    if not M:-UsesArgsOrNargs(newProc) then
        env := callStack:-topEnv();
        newParamList := select(x -> env:-isDynamic(op(1,x)), params);
        newProc := subsop(1=newParamList, newProc);
    end if;
    
    if n <> "" then
       code[n] := newProc;
    end if;
    newProc;    
end proc; 


# Given an inert procedure and an inert function call to that procedure, decide if unfolding should be performed.
# probably won't be needed if I go with the sp-function approach
isUnfoldable := proc(inertProcedure::m(Proc))
    if not callStack:-inConditional() then
        return true;
    end if;
    flattened := flattenStatseq(getProcBody(inertProcedure));
    # if all the func does is return a static value then there is no reason not to unfold
    evalb( nops(flattened) = 1 and op([1,0], flattened) = _Inert_RETURN and isStaticValue(op([1,1], flattened)) );
end proc;


# partially evaluates an arbitrary M code
peM := proc(m::m) local header; # returns inert code or NULL    
    header := M:-Header(m);
    if assigned(pe[header]) then
        return pe[header](op(m));
    end if;
    error cat("not supported yet: ", header);
end proc;


pe[MStandaloneExpr] := e -> MStandaloneExpr(ReduceExp(e, callStack:-topEnv()));
pe[MReturn] := e -> MReturn(ReduceExp(e, callStack:-topEnv()));


pe[MStatSeq] := proc()
    q := SimpleQueue();
    for i from 1 to nargs do
        res := peM([args][i]);
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
    reduced := ReduceExp(cond, callStack:-topEnv());
    
    # Can't just copy the environment and put a new copy on the stack
    # because there may exist closures that referece the environment.
    if M:-IsM(reduced) then
        callStack:-setConditional();
        env := callStack:-topEnv();
        original := env:-clone();
        
        reds1 := peM(s1);
        thenEnv := env:-clone();
        env:-overwrite(original);
        reds2 := peM(s2);
        elseEnv := env:-clone();
        
        # TODO, is this required? no because of INF
        env:-overwrite(thenEnv:-combine(elseEnv));
        callStack:-setConditional(false);
        
        # if reds1 and reds2 are both empty then its a no-op
        if reds1 = MStatSeq() and reds2 = MStatSeq() then
            MStatSeq();
        else
            MIfThenElse(reduced, reds1, reds2);
        end if;        
    else
        peM(`if`(reduced, s1, s2))
    end if;
end proc;


pe[MAssign] := proc(n::m(Local), expr::m)
	env := callStack:-topEnv();
    reduced := ReduceExp(expr, env);
    if M:-IsM(reduced) then
        MAssign(n, reduced);
    else
        env:-putVal(op(n), reduced);
        NULL;
    end if;
end proc;  



pe[MStandaloneFunction] := proc(n::m({AssignedName, Param, Local}))
    unfold := proc(residualProcedure, redCall, fullCall)
        M:-Unfold:-UnfoldStandalone(residualProcedure, redCall, fullCall, gen);
    end proc;
    peFunction(args, unfold, ()-> args);    
end proc;



pe[MAssignToFunction] := proc(var::m(GeneratedName), funcCall::m(Function))     
    unfold := proc(residualProcedure, redCall, fullCall)
        res := M:-Unfold:-UnfoldIntoAssign(residualProcedure, redCall, fullCall, gen, var);
        flattened := M:-FlattenStatSeq(res);

        # If resulting statseq has only one statment then
        # it must be an assign because thats what UnfoldIntoAssign does
        if nops(flattened) = 1 then            
            assign := op(flattened);
            expr := op(2, assign);
            val := getStaticValue(expr);
            if val <> FAIL then
                varName := op([1,1], assign);
                callStack:-topEnv():-putVal(varName, val);                
                return NULL;            
            end if;
        end if;
        flattened;
    end proc;    
    peFunction(op(funcCall), unfold, x -> MAssign(var, x));    
end proc;



peArgList := proc(params::m(ParamSeq), argExpSeq::m(ExpSeq))	   	   	
   	env := OnENV(); # new env for function call
   	allNotExpSeqSoFar := true; # true until something possibly an expseq is reached   	
   	fullCall := SimpleQueue(); # residual function call including statics
   	redCall  := SimpleQueue(); # residual function call without statics   	 
   	argsTbl := table(); # mappings for args
   	
   	top := callStack:-topEnv(); 
   	i := 0; 
   	
   	for arg in argExpSeq do
   	    i := i + 1;
   	    reduced := ReduceExp(arg, top);   	    
   	    fullCall:-enqueue(reduced);
   	    
   	    if M:-IsM(reduced) then
   	        redCall:-enqueue(reduced);
   	        if Header(reduced) = MParam and allNotExpSeqSoFar then
   	            #argsTbl[i] := reduced;
   	            # unsound, what if proc dosen't unfold?
   	        else
   	            allNotExpSeqSoFar := false;
   	        end if;   	    
   	    else
   	        if allNotExpSeqSoFar then
   	            if i <= nops(params) then
   	                env:-putVal(op(op(i, params)), reduced);
   	            end if;
   	            argsTbl[i] := reduced;
   	        else
   	            redCall:-enqueue(reduced);
   	        end if;   	    
   	    end if;
   	end do;
    if allNotExpSeqSoFar then
        env:-setNargs(i);
    end if;
 
    env:-setArgs(argsTbl);    
    toExpSeq := q -> MExpSeq(op(q:-toList()));    
    return env, toExpSeq(redCall), toExpSeq(fullCall);
end proc;



# takes continuations to be applied if f results in a procedure
peFunction := proc(f::m, argExpSeq::m(ExpSeq), unfold::procedure, residualize::procedure) :: m;
    fun := ReduceExp(f, callStack:-topEnv());
    
    if M:-IsM(fun) then
        # don't know what function was called, residualize call
        MFunction(fun, map(peResidualizeExpr, argExpSeq));
        
    elif type(fun, procedure) then
	    m := getMCode(fun);
	    newEnv, redCall, fullCall := peArgList(M:-Params(m), argExpSeq);
	    #mapLocalsToSymbols(newEnv, M:-Locals(m));
	    #build a new environment for the function
	    callStack:-push(newEnv);
	    newName := gen(cat(op(1,f),"_"));
	    
	    newProc := peSpecializeProc(m, newName);
	    
	    callStack:-pop();
	    
	    if isUnfoldable(newProc) then
	        code[newName] := evaln(code[newName]); # remove mapping from code
	        unfold(newProc, redCall, fullCall);
	    elif M:-UsesArgsOrNargs(Body(newProc)) then
	        residualize(fullCall)
	    else
	        residualize(redCall)
	    end if;
	    
    elif Header(fun) = Closure then
        # TODO, the full functionality of peArgList is not needed here
        newEnv, _ := peArgList(M:-Params(Code(fun)), argExpSeq); 
        # attach lexical environment to the environment of the function
        #mapLocalsToSymbols(newEnv, M:-Locals(Code(fun)));
        newEnv:-attachLex(Lex(fun));
        callStack:-push(newEnv);
        res := peSpecializeProc(Code(fun));
        callStack:-pop();
        newEnv:-removeLex();       
        # should probably be a proper unfolding
        M:-ProcBody(res);
    
    elif Header(fun) = SModuleLocal and type(op(2,fun), procedure) then

        error "hard stop";
        #p := op(2, fun);        
        #m := getMCode(p);
        #newEnv, newArgs := peArgList(M:-Params(m), argExpSeq);
        
    else
        error "received unknown form";
    end if;
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
                if not member(localName, locals, localIndex) then #nasty!
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
