# Simple online partial evaluator for a subset of maple

OnPE := module() option package;

    description "online partial evaluator for a subset of Maple";
    local callStack, code, gen, genv,
          CallStack;
    export Debug, ModuleApply, PartiallyEvaluate, OnENV, ReduceExp, Lifter;

ModuleApply := PartiallyEvaluate;

$include "access.mpl"
$include "pe_stack.mpl"
$include "pe_onenv.mpl";
$include "pe_reduce_exp.mpl"
$include "pe_lift.mpl"
$include "pe_module.mpl"
$include "pe_debug.mpl"


##################################################################################
# utility functions used by this package

# caches M code of procedures so don't need to call ToM unneccesarily
getMCode := proc(fun) option cache;
    M:-ToM(ToInert(fun))
end proc;


embed := proc(e)
    if nargs = 0 then
        MStatic()
    elif nargs = 1 and e::Static then
        MStatic(e)
    elif nargs = 1 and e::Dynamic then
        e
    elif [args] :: list(Static) then
        MStatic(args);
    else
        error "illegal embed: %1", [args];
    end if;
end proc;



############################################################################
# The specializer
############################################################################


Debug := proc(p, num)
    try
        if nargs = 2 then
            PEDebug:-RunThenStop(num);
        else
            PEDebug:-Begin();
        end if;
    catch "debug":
        lprint("debug session exited");
        return;
    end try;
    PartiallyEvaluate(p);
end proc;

# called with a procedure, name of residual proc, and a list of equations
# sets up the partial evaluation
PartiallyEvaluate := proc(p)
    # need access to module locals
    before := kernelopts(opaquemodules=false);
    
    # set up module locals
    gen := NameGenerator();
    callStack := CallStack();
    code := table();
    genv := OnENV(); # the global environment

    m := getMCode(eval(p));

    newEnv := OnENV();
    newEnv:-setArgs(table());
    callStack:-push(newEnv);
    
    try
        peSpecializeProc(m, "ModuleApply");
        Lifter:-LiftPostProcess(code);
    catch "debug":
        lprint("debug session exited");
        lprint(PEDebug:-GetStatementCount(), "statements partially evaluated");
        return;
    catch:
        lprint(PEDebug:-GetStatementCount(), "statements partially evaluated before error");
        error;
        #print(lastexception);
        #return copy(code);
    end try;
    
    try
        inertModule := BuildModule("ModuleApply");
    catch:
        lprint("conversion to inert module failed", lastexception);
        return copy(code);
    end try;
    
    try
        res := eval(FromInert(inertModule));
    catch:
        lprint("FromInert on inertModule failed", lastexception);
        return copy(code);
    end try;

    # unassign module locals
    gen := 'gen';
    code := 'code';
    genv := 'genv';
    callStack := 'callStack';
    kernelopts(opaquemodules=before);

    print(PEDebug:-GetStatementCount(), "statements processed. Success!");
    return res;
end proc;



# takes inert code and assumes static variables are on top of callStack
# called before unfold
peSpecializeProc := proc(m::mform(Proc), n::string := "") :: mform(Proc);    
    # attach lexical environment
    env := callStack:-topEnv();
    if not env:-hasLex() then
        lexMap := M:-CreateLexNameMap(LexSeq(m), curry(op,2));
        env:-attachLex(lexMap);
    end if;
    
    # create static locals
    for loc in Locals(m) do
        varName := Var(loc);
        env:-putVal(varName, convert(varName, `local`));
    end do;

    body := M:-AddImplicitReturns(ProcBody(m)); # if a block ends with an assignment
    body := peM(body); # Partial Evaluation

    newProc := subsop(5=body, m);
    newProc := M:-SetArgsFlags(newProc);

    if not M:-UsesArgsOrNargs(newProc) then
        newParamList := select(x -> env:-isDynamic(op(1,x)), Params(m));
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
    
    # if the body of the function is empty then go ahead and unfold
    if nops(flattened) = 0 then
        true
    else
        # if the function body consists of a single static than it can be easily unfolded
        nops(op([1,1], flattened)) = 1 
        and member(op([1,0], flattened), {MReturn, MStandaloneExpr})
        and op([1,1], flattened)::Static
    end if;
end proc;


# partially evaluates an arbitrary M code
peM := proc(m::mform)
    h := Header(m);
    if assigned(pe[h]) then
        return pe[h](op(m));
    end if;
    error "(peM) not supported yet: %1", h;
end proc;


peResidualize := (f, e) -> f(ReduceExp(e));

pe[MStandaloneExpr] := curry(peResidualize, MStandaloneExpr);
pe[MReturn] := curry(peResidualize, MReturn);
pe[MError]  := curry(peResidualize, MError);



pe[MStatSeq] := proc() :: mform(StatSeq);
    q := SimpleQueue();
    for i from 1 to nargs do
        stmt := args[i];
        h := Header(stmt);

        PEDebug:-StatementStart(stmt);

        if h = MIfThenElse then
            q:-enqueue(peIF(stmt, MStatSeq(args[i+1..nargs])));
            PEDebug:-StatementEnd();
            break;
        end if;

        residual := peM(stmt);
        
        PEDebug:-StatementEnd(residual);

        if residual <> NULL then
            if op(0,residual) = MTry and i < nargs then
                error "code after a try/catch is not supported";
            end if;
            q:-enqueue(residual);
            if M:-EndsWithErrorOrReturn(residual) then
                break
            end if;
        end if;
    end do;
    #`if`(q:-empty(), NULL, MStatSeq(qtoseq(q)))
    # TODO, removing usless exprs now is a bit of a hack, a postprocess would be better
    M:-RemoveUselessStandaloneExprs(MStatSeq(qtoseq(q)));
end proc;


peIF := proc(ifstat::mform(IfThenElse), S::mform(StatSeq))
    rcond := ReduceExp(Cond(ifstat));
    if rcond::Static then
        PEDebug:-Message(evalb(SVal(rcond)));
        stmts := `if`(SVal(rcond), Then(ifstat), Else(ifstat));
        peM(MStatSeq(ssop(stmts), ssop(S)));
    else
        callStack:-setConditional();
        env := callStack:-topEnv();
        PEDebug:-Message("grow");
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



pe[MAssign] := proc(n::mform({Local, Name, AssignedName, Catenate, GeneratedName}), expr::mform)
    reduced := ReduceExp(expr);

    # use the appropriate environment based on the scope of the variable
    env := `if`(Header(n)=MLocal, callStack:-topEnv(), genv);

    if Header(n) = MCatenate then
        var := ReduceExp(n);
        if var::Dynamic then
            return MAssign(n, reduced); # TODO, maybe don't use n
        elif nops([SVal(var)]) <> 1 then
            error "multiple assignment not supported"
        else
            var := convert(SVal(var), string);
        end if
    else
        var := Name(n);
    end if;

    if reduced::Static then
        env:-putVal(var, SVal(reduced));
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
        env:-putTblVal(var, SVal(rindex), SVal(rexpr));
        return NULL;
    end if;
    #print("table assign generating code");
    #print("rindex", type(rindex, Static));
    #print("rexpr", type(rexpr, Static));
    #print("IndexExp(tr)", IndexExp(tr));
    #print("expr", expr);
    #print("rexpr", rexpr);
    #print();
    if rindex::Static then
        env:-setTblValDynamic(var, SVal(rindex));
        MTableAssign(subsop(2=rindex, tr), rexpr);
    else
        env:-setValDynamic(var);
        MTableAssign(subsop(2=rindex, tr), rexpr);
    end if;
end proc;


# returns an object that can be used to unroll the body of a loop
StaticLoopUnroller := proc(loopVar, statseq) :: `module`;
    if loopVar <> MExpSeq() then
        loopVarName := Name(loopVar);
    end if;
    env := callStack:-topEnv();
    q := SimpleQueue();
    
    return module() export unrollOnce, result;    
        unrollOnce := proc(i) # pass in the loop index
            if assigned(loopVarName) then
                env:-putVal(loopVarName, i, 'readonly');                
            end if;
            res := peM(statseq);
            if res <> NULL then
                q:-enqueue(res);
            end if;        
        end proc;       
        result := () -> MStatSeq(qtoseq(q));        
    end module;
end proc;


pe[MForFrom] := proc(loopVar::mform({Local, ExpSeq}), fromExp, byExp, toExp, statseq)
    rFromExp := ReduceExp(fromExp);
    rByExp   := ReduceExp(byExp);
    rToExp   := ReduceExp(toExp);
    
    if [rFromExp,rByExp,rToExp]::[Static,Static,Static] then #unroll loop        
        rFromExp := SVal(rFromExp);
        rByExp := SVal(rByExp);
        rToExp := SVal(rToExp);
        
        unroller := StaticLoopUnroller(loopVar, statseq);
        for i from rFromExp by rByExp to rToExp do
            unroller:-unrollOnce(i);
        end do;        
        unroller:-result();
    else
        error "dynamic loops not supported yet";
    end if;
end proc;




pe[MForIn] := proc(loopVar, inExp, statseq)
    rInExp := ReduceExp(inExp);
    if [rInExp]::list(Static) then
        unroller := StaticLoopUnroller(loopVar, statseq);
        for i in SVal(rInExp) do
            unroller:-unrollOnce(i);
        end do;
        return unroller:-result();
    else
        error "dynamic loops not supported yet";
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
    MTry(rtry, MCatchSeq(qtoseq(q)), rfin);
end proc;



pe[MStandaloneFunction] := proc()
    unfold := proc(residualProcedure, redCall, fullCall)
        M:-Unfold:-UnfoldStandalone(residualProcedure, redCall, fullCall, gen);
        #flattened := M:-FlattenStatSeq(res);
        #if nops(flattened) = 1 and op([1,0], flattened) = MStandaloneExpr then
        #    NULL
        #else
        #    flattened;
        #end if;
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
                #return symbolic(expr);
                callStack:-topEnv():-putVal(op(var), SVal(expr));
                return NULL;
            end if;
        end if;
        #print("returning flattened", nops(flattened));
        #if nops(flattened) = 1 then
        #    for w in flattened do
        #        print(w);
        #    end do;
        #    callStack:-topEnv():-display();
        #end if;
        flattened;
    end proc;

    residualize := proc()
        callStack:-topEnv():-setValDynamic(var);
        MAssignToFunction(var, MFunction(args));
    end proc;

    symbolic := proc(s)
        callStack:-topEnv():-putVal(op(var), SVal(s));
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
   	            #error "what?"; #TODO, what?
   	        else
   	            allNotExpSeqSoFar := false;
   	        end if;
   	    else
   	        if allNotExpSeqSoFar then
   	            if i <= nops(params) then
   	                env:-putVal(op(op(i, params)), SVal(reduced));
   	            end if;
   	            argsTbl[i] := SVal(reduced);
   	        else
   	            redCall:-enqueue(reduced);
   	        end if;
   	    end if;
   	end do;
    if allNotExpSeqSoFar then
        env:-setNargs(i);
    end if;

    env:-setArgs(argsTbl);
    toExpSeq := q -> MExpSeq(qtoseq(q));
    return env, toExpSeq(redCall), toExpSeq(fullCall);
end proc;



# takes continuations to be applied if f results in a procedure
peFunction := proc(f, argExpSeq::mform(ExpSeq), unfold::procedure, residualize::procedure, symbolic::procedure)
    local sfun;
    PEDebug:-FunctionStart(f);
    fun := ReduceExp(f);

    if fun::Dynamic then
        # don't know what function was called, residualize call
        res := residualize(fun, ReduceExp(argExpSeq));
        PEDebug:-FunctionEnd();
        return res;
    end if; 
    
    sfun := SVal(fun);
    
    if type(eval(sfun), `procedure`) then
        newName := gen(cat(op(1,f),"_"));
        res := peRegularFunction(eval(sfun), argExpSeq, unfold, residualize, newName);
        
    elif Header(sfun) = SPackageLocal and type(Member(sfun), `procedure`) then
        mem := Member(sfun);
        res := peRegularFunction(mem, argExpSeq, unfold, residualize, gen("fun"));

	elif type(sfun, `module`) then
	    if member(convert("ModuleApply",name), sfun) then
	        ma := sfun:-ModuleApply;
	    else
            ma := op(select(x->evalb(convert(x,string)="ModuleApply"), [op(3,eval(sfun))]));
            if ma = NULL then error "package does not contain ModuleApply" end if;
        end if;
	    res := peRegularFunction(ma, argExpSeq, unfold, residualize, gen("ma"));
    else
        redargs := ReduceExp(argExpSeq);
        if [redargs]::list(Static) then
            res := symbolic(MStatic( apply(sfun, SVal(redargs)) ));
        else
            res := residualize(fun, MExpSeq(redargs));
        end if;

    end if;
    res;
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




end module:
