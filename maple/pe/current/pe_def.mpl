# Simple online partial evaluator for a subset of maple

OnPE := module() option package;

    description "online partial evaluator for a subset of Maple";
    local callStack, code, gen,
          CallStack, stmtCount;
    export ModuleApply, PartiallyEvaluate, OnENV, ReduceExp, Lifter;

ModuleApply := PartiallyEvaluate;


$include "pe_stack.mpl"

$include "pe_onenv.mpl";

$include "pe_reduce_exp.mpl"

$include "pe_lift.mpl"

##################################################################################
# utility functions used by this package

# caches M code of procedures so don't need to call ToM unneccesarily
getMCode := proc(fun) option cache;
    M:-ToM(ToInert(fun))
end proc;


keys := proc(tbl) option inline;
    map(op, [indices(tbl)])
end proc;

Header := proc(x) option inline; op(0,x) end proc;
# for dealing with closures
Lex  := proc(x) option inline; op(1,x) end proc;
Code := proc(x) option inline; op(2,x) end proc;

Package := proc(x) option inline; op(1,x) end proc;
Member := proc(x) option inline; op(2,x) end proc;


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
#                error "Type assertion falure" ;
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
    before := kernelopts(opaquemodules=false);

    # set up module locals
    gen := NameGenerator();
    callStack := CallStack();
    code := table();
    stmtCount := 0;

    m := getMCode(eval(p));
    #print(m);
    #error "hard stop";

    newEnv := OnENV();
    newEnv:-setArgs(table());
    #mapLocalsToSymbols(newEnv, M:-Locals(m));
    callStack:-push(newEnv);

    try
        # perform partial evaluation
        peSpecializeProc(m, "ModuleApply");
    catch:
        lprint(stmtCount, "statements partially evaluated before error");
        error;
    end try;

    Lifter:-LiftPostProcess(code);

    try
        res := (eval @ FromInert @ build_module)("ModuleApply");
    catch:
        lprint("conversion to module failed", lastexception);
        return copy(code)
    end try;

    # unassign module locals
    gen := 'gen';
    callStack := 'callStack';
    code := 'code';
    kernelopts(opaquemodules=before);

    print(stmtCount, "statements processed");
    return res;
end proc;



# takes inert code and assumes static variables are on top of callStack
# called before unfold
peSpecializeProc := proc(m::mform(Proc), n::string := "") :: mform(Proc);
    params := M:-Params(m);
    body   := M:-ProcBody(m);

    body := M:-TransformIfNormalForm(body);
    body := M:-AddImplicitReturns(body);

    env := callStack:-topEnv();
    if not env:-hasLex() then
        lexMap := M:-CreateLexNameMap(M:-LexSeq(m), curry(op,2));
        env:-attachLex(lexMap);
    end if;
    env:-attachGlobals(M:-GlobalSeq(m));

    body := peM(body); # Partial Evaluation

    newProc := subsop(5=body, m);
    newProc := M:-SetArgsFlags(newProc);

    if not M:-UsesArgsOrNargs(newProc) then
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
isUnfoldable := proc(inertProcedure::mform(Proc))
    if not callStack:-inConditional() then
        return true;
    end if;
    flattened := M:-FlattenStatSeq(M:-ProcBody(inertProcedure));
    # if all the func does is return a static value then there is no
    # reason not to unfold
    evalb( nops(flattened) = 1 # function body has only one statement
       and member(op([1,0], flattened), {MReturn, MStandaloneExpr})
       and not type(op([1,1], flattened), mform) )
end proc;


# partially evaluates an arbitrary M code
peM := proc(m::mform) local header; # returns inert code or NULL
    header := M:-Header(m);
    if assigned(pe[header]) then
        return pe[header](op(m));
    end if;
    error "not supported yet: %1", header;
end proc;


peResid := (f, e) -> f(ReduceExp(e));

pe[MStandaloneExpr] := curry(peResid, MStandaloneExpr);
pe[MReturn] := curry(peResid, MReturn);
pe[MError]  := curry(peResid, MError);



pe[MStatSeq] := proc() :: mform(StatSeq);
    q := SimpleQueue();
    for i from 1 to nargs do
        stmtCount := stmtCount + 1;

        if true then
            print();
            print("stat");
            if member(Header(args[i]), {MIfThenElse, MTry}) then
    	        print(Header(args[i]));
    	    else
    	        print(args[i]);
    	    end if;
    	    print();
	    end if;

        res := peM([args][i]);
        if nops([res]) > 0 then
            if op(0,res) = MTry and i < nargs then
                error "code after a try/catch is not supported";
            end if;
            q:-enqueue(res);
            if M:-EndsWithErrorOrReturn(res) then
                break
            end if;
        end if;
    end do;
    MStatSeq(op(q:-toList()));
end proc;


pe[MIfThenElse] := proc(cond, s1, s2)
    reduced := ReduceExp(cond);

    # Can't just copy the environment and put a new copy on the stack
    # because there may exist closures that referece the environment.
    if reduced::Dynamic then
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


pe[MAssign] := proc(n::mform(Local), expr::mform)
    reduced := ReduceExp(expr);
    if reduced::Dynamic then
        MAssign(n, reduced);
    else
        callStack:-topEnv():-putVal(op(n), reduced);
        NULL;
    end if;
end proc;


pe[MTableAssign] := proc(tr::mform(Tableref), expr::mform)
    red1 := ReduceExp(M:-IndexExp(tr));
    red2 := ReduceExp(expr);

    env := callStack:-topEnv();
    if [red1,red2]::[Static,Static] then
        var := M:-Var(tr);
        if env:-isDynamic(op(var)) then
            # tables can be implicitly created in Maple, so create a table on-the-fly if needed
            tbl := table();
            env:-putVal(op(var), tbl);
        else
            tbl := env:-getVal(op(var));
        end if;
        tbl[red1] := red2;
        NULL;
    else
        MTableAssign(subsop(2=red1, tr), red2);
    end if;

end proc;



pe[MTry] := proc(tryBlock, catchSeq, finallyBlock)
    rtry := peM(tryBlock);

    if rtry = NULL then
        return NULL;
    elif nops(rtry) = 1 then
        stat := op(1,rtry);
        if member(Header(stat), {MReturn, MStandaloneExpr}) and op(1,stat)::Static then
            return stat;
        end if;
    end if;

    #top := callStack:-pop();
    q := SimpleQueue();

    for c in catchSeq do
        callStack:-push();
        rcat := peM(M:-CatchBody(c));
        if M:-HasVariable(rcat) then
            error "variables in catch block not supported";
        end if;
        q:-enqueue(MCatch(M:-CatchString(c), rcat));
        callStack:-pop();
    end do;

    rfin := NULL;
    if nargs = 3 then # there is a finally block
        callStack:-push();
        rfin := peM(op(finallyBlock));
        if M:-HasVariable(rfin) then
            error "variables in finally block not supported";
        end if;
        callStack:-pop();
    end if;

    #callStack:-push(top);
    MTry(rtry, MCatchSeq(op(q:-toList())), rfin);
end proc;



pe[MStandaloneFunction] := proc()
    unfold := proc(residualProcedure, redCall, fullCall)
        M:-Unfold:-UnfoldStandalone(residualProcedure, redCall, fullCall, gen);
    end proc;
    residualize := ()-> MStandaloneFunction(args);
    symbolic := () -> MStandaloneExpr(args);
    peFunction(args, unfold, residualize, symbolic);
end proc;



pe[MAssignToFunction] := proc(var::mform(GeneratedName), funcCall::mform(Function))
    unfold := proc(residualProcedure, redCall, fullCall)
        res := M:-Unfold:-UnfoldIntoAssign(residualProcedure, redCall, fullCall, gen, var);
        flattened := M:-FlattenStatSeq(res);
        # If resulting statseq has only one statment then
        # it must be an assign because thats what UnfoldIntoAssign does
        if nops(flattened) = 1 then
            assign := op(flattened);
            expr := op(2, assign);
            if expr::Static then
                #varName := op([1,1], assign);
                return symbolic(expr);
                #callStack:-topEnv():-putVal(varName, expr);
                #return NULL;
            end if;
        end if;
        flattened;
    end proc;

    residualize := () -> MAssignToFunction(var, MFunction(args));

    symbolic := proc(s)
        callStack:-topEnv():-putVal(op(var), s);
        NULL;
    end proc;

    peFunction(op(funcCall), unfold, residualize, symbolic);
end proc;



peArgList := proc(params::mform(ParamSeq), argExpSeq::mform(ExpSeq))
   	env := OnENV(); # new env for function call
   	allNotExpSeqSoFar := true; # true until something possibly an expseq is reached
   	fullCall := SimpleQueue(); # residual function call including statics
   	redCall  := SimpleQueue(); # residual function call without statics
   	argsTbl := table(); # mappings for args

   	i := 0;

   	for arg in argExpSeq do
   	    i := i + 1;
   	    reduced := ReduceExp(arg);
   	    fullCall:-enqueue(reduced);

   	    if reduced::Dynamic then
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
peFunction := proc(f, argExpSeq::mform(ExpSeq), unfold::procedure, residualize::procedure, symbolic::procedure)
    fun := ReduceExp(f);

    if fun::Dynamic then
        # don't know what function was called, residualize call
        MFunction(fun, ReduceExp(argExpSeq));

    elif type(eval(fun), `symbol`) then
        redargs := ReduceExp(argExpSeq);
        if [redargs]::list(Static) then
            symbolic(fun(redargs));
        else
            residualize(fun, MExpSeq(redargs));
        end if;

    elif Header(fun) = Closure then
        # TODO, the full functionality of peArgList is not needed here
        newEnv, a, b := peArgList(M:-Params(Code(fun)), argExpSeq);
        # attach lexical environment to the environment of the function
        newEnv:-attachLex(Lex(fun));
        callStack:-push(newEnv);
        res := peSpecializeProc(Code(fun));
        callStack:-pop();
        newEnv:-removeLex();
        # should probably be a proper unfolding
        M:-ProcBody(res);

    elif type(eval(fun), `procedure`) then
        newName := gen(cat(op(1,f),"_"));
        peRegularFunction(eval(fun), argExpSeq, unfold, residualize, newName);

    elif Header(fun) = SPackageLocal and type(Member(fun), `procedure`) then
        mem := Member(fun);
        peRegularFunction(mem, argExpSeq, unfold, residualize, gen("fun"));

	elif type(fun, `module`) then
	    if member(convert("ModuleApply",name), fun) then
	        ma := fun:-ModuleApply;
	    else
            ma := op(select(x->evalb(convert(x,string)="ModuleApply"), [op(3,eval(fun))]));
            if ma = NULL then error "package does not contain ModuleApply" end if;
        end if;
	    peRegularFunction(ma, argExpSeq, unfold, residualize, gen("ma"));

    else
        error "received unknown form %1, %2", fun;
    end if;
end proc;


# partial evaluation of a known procedure
peRegularFunction := proc(fun::procedure, argExpSeq::mform(ExpSeq), unfold, residualize, newName)
	m := getMCode(eval(fun));

    newEnv, redCall, fullCall := peArgList(M:-Params(m), argExpSeq);
#    lexMap := M:-CreateLexNameMap(M:-LexSeq(m), curry(op,2));
#    newEnv:-attachLex(lexMap);

    callStack:-push(newEnv);
    newProc := peSpecializeProc(m, newName);
    callStack:-pop();

    if isUnfoldable(newProc) then
        code[newName] := evaln(code[newName]); # remove mapping from code
        unfold(newProc, redCall, fullCall);
    elif M:-UsesArgsOrNargs(newProc) then
        residualize(MString(newName), fullCall)
    else
        residualize(MString(newName), redCall)
    end if;
end proc;



########################################################################################


#builds a modle definition that contains the residual code
build_module := proc(n::string)::inert;
    # get a list of names of module locals
    # n will be the export so remove it from this list
    locals := remove(`=`, keys(code), n);

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
                    return _Inert_FUNCTION(args); #error "%1 is not a module local", localName;
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

        lseq := map(f, lexicalLocals);

        lexicalLocals := _Inert_LEXICALSEQ( op(lseq) );
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
