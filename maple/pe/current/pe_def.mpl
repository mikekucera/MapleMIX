# Simple online partial evaluator for a subset of maple

OnPE := module() option package;

    description "online partial evaluator for a subset of Maple";
    local callStack, code, gen, genv,
          CallStack, stmtCount;
    export ModuleApply, PartiallyEvaluate, OnENV, ReduceExp, Lifter;

ModuleApply := PartiallyEvaluate;

$include "access.mpl"
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

ssop := M:-ssop;

############################################################################
# The specializer
############################################################################


# called with a procedure, name of residual proc, and a list of equations
# sets up the partial evaluation
PartiallyEvaluate := proc(p)#::procedure)
    # need access to module locals
    before := kernelopts(opaquemodules=false);

    # set up module locals
    gen := NameGenerator();
    callStack := CallStack();
    code := table();
    genv := OnENV(); # the global environment
    stmtCount := 0;

    m := getMCode(eval(p));

    newEnv := OnENV();
    newEnv:-setArgs(table());
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
        res := eval(FromInert(build_module("ModuleApply")));
    catch:
        lprint("conversion to module failed", lastexception);
        return copy(code);
    end try;

    # unassign module locals
    gen := 'gen';
    code := 'code';
    genv := 'genv';
    callStack := 'callStack';
    kernelopts(opaquemodules=before);

    print(stmtCount, "statements processed");
    return res;
end proc;



# takes inert code and assumes static variables are on top of callStack
# called before unfold
peSpecializeProc := proc(m::mform(Proc), n::string := "") :: mform(Proc);
    params := Params(m);
    body   := ProcBody(m);

    body := M:-AddImplicitReturns(body); # if a block ends with an assignment

    env := callStack:-topEnv();
    if not env:-hasLex() then
        lexMap := M:-CreateLexNameMap(LexSeq(m), curry(op,2));
        env:-attachLex(lexMap);
    end if;

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
    flattened := M:-FlattenStatSeq(ProcBody(inertProcedure));
    # if all the func does is return a static value then there is no
    # reason not to unfold
    evalb( nops(flattened) = 1 # function body has only one statement
       and member(op([1,0], flattened), {MReturn, MStandaloneExpr})
       and not type(op([1,1], flattened), mform) )
end proc;


# partially evaluates an arbitrary M code
peM := proc(m::mform)
    h := Header(m);
    if assigned(pe[h]) then
        return pe[h](op(m));
    end if;
    error "(peM) not supported yet: %1", h;
end proc;


peResid := (f, e) -> f(ReduceExp(e));

pe[MStandaloneExpr] := curry(peResid, MStandaloneExpr);
pe[MReturn] := curry(peResid, MReturn);
pe[MError]  := curry(peResid, MError);



pe[MStatSeq] := proc() :: mform(StatSeq);
    q := SimpleQueue();
    for i from 1 to nargs do
        stmtCount := stmtCount + 1;
        stmt := args[i];
        h := Header(stmt);

        if false then
            print(); print("stat");
            if member(h, {MIfThenElse, MTry}) then
    	        print(h);print();
    	    else
    	        print(stmt);print();
    	    end if;
	    end if;

        if h = MIfThenElse then
            q:-enqueue(peIF(stmt, MStatSeq(args[i+1..nargs])));
            break;
        end if;

        res := peM(stmt);

        if res <> NULL then
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


peIF := proc(ifstat::mform(IfThenElse), S::mform(StatSeq))
    rcond := ReduceExp(Cond(ifstat));
    if rcond::Static then
        stmts := `if`(rcond, Then(ifstat), Else(ifstat));
        peM(MStatSeq(ssop(stmts), ssop(S)));
    else
        callStack:-setConditional();
        env := callStack:-topEnv();
        env:-grow();
        genv:-grow();

        C1 := peM(Then(ifstat));

        prevTopLocal  := env:-markTop();
        prevTopGlobal := genv:-markTop();

        S1 := peM(S);

        env:-shrinkGrow();
        genv:-shrinkGrow();

        C2 := peM(Else(ifstat));

        if env:-equalsTop(prevTopLocal) and genv:-equalsTop(prevTopGlobal) then
            env:-shrink();
            genv:-shrink(); # TODO, not needed
            MStatSeq(MIfThenElse(rcond, C1, C2), ssop(S1));
        else
            S2 := peM(S);
            env:-shrink();
            genv:-shrink(); # TODO, not needed
            MIfThenElse(rcond, MStatSeq(ssop(C1), ssop(S1)), MStatSeq(ssop(C2), ssop(S2)));
        end if;
    end if
end proc;



pe[MAssign] := proc(n::mform({Local, Name, AssignedName, Catenate}), expr::mform)
    reduced := ReduceExp(expr);

    # use the appropriate environment based on the scope of the variable
    env := `if`(Header(n)=MLocal, callStack:-topEnv(), genv);

    if Header(n) = MCatenate then
        var := ReduceExp(n);
        if nops([var]) <> 1 then
            error "multiple assignment not supported"
        elif var::Dynamic then
            # TODO, maybe don't use n
            return MAssign(n, reduced);
        else
            var := convert(var, string);
        end if
    else
        var := Name(n);
    end if;

    if reduced::Static then
        env:-putVal(var, reduced);
        NULL;
    else
        env:-setValDynamic(var);
        MAssign(n, reduced);
    end if;
end proc;



pe[MTableAssign] := proc(tr::mform(Tableref), expr::mform)
    rindex := ReduceExp(IndexExp(tr));
    rexpr  := ReduceExp(expr);

    env := `if`(Header(Var(tr))=MLocal, callStack:-topEnv(), genv);

    var := Name(Var(tr));

    if [rindex,rexpr]::[Static,Static] then
        env:-putTblVal(var, rindex, rexpr);
    callStack:-topEnv():-display();
        NULL;
    elif rindex::Static then
        env:-setTblValDynamic(var, rindex);
    callStack:-topEnv():-display();
        MTableAssign(subsop(2=rindex, tr), rexpr);
    else
        env:-setValDynamic(var);
    callStack:-topEnv():-display();
        MTableAssign(subsop(2=rindex, tr), rexpr);
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
        rcat := peM(CatchBody(c));
        if M:-HasVariable(rcat) then
            error "variables in catch block not supported";
        end if;
        q:-enqueue(MCatch(CatchString(c), rcat));
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
        newEnv, a, b := peArgList(Params(Code(fun)), argExpSeq);
        # attach lexical environment to the environment of the function
        newEnv:-attachLex(Lex(fun));
        callStack:-push(newEnv);
        res := peSpecializeProc(Code(fun));
        callStack:-pop();
        newEnv:-removeLex();
        # should probably be a proper unfolding
        ProcBody(res);

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

    newEnv, redCall, fullCall := peArgList(Params(m), argExpSeq);
#    lexMap := M:-CreateLexNameMap(LexSeq(m), curry(op,2));
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
            if Header(n) = _Inert_ASSIGNEDNAME then
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


        body := eval(ProcBody(p), _Inert_FUNCTION = processFuncCall);

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
