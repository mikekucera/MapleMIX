# Simple online partial evaluator for a subset of maple

OnPE := module() option package;

    description "online partial evaluator for a subset of Maple";
    local callStack, code, gen, genv, gopts,
          CallStack, Unfold;
    export Debug, ModuleApply, PartiallyEvaluate, OnENV, ReduceExp, Lifter, isPossibleExpSeq;

ModuleApply := PartiallyEvaluate;

use PEOptions in

$include "access.mpl"
$include "pe_stack.mpl"
$include "pe_onenv.mpl";
$include "pe_reduce_exp.mpl"
$include "pe_lift.mpl"
$include "pe_module.mpl"
$include "pe_debug.mpl"
$include "pe_unfold.mpl"


############################################################################
# The specializer
############################################################################

# sets up the partial evaluation
PartiallyEvaluate := proc(p::`procedure`, opts::`module`:=PEOptions())
    # need access to module locals
    before := kernelopts(opaquemodules=false);
    gopts := opts;
    
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
        peFunction_GenerateNewSpecializedProc(m, "ModuleApply");
        Lifter:-LiftPostProcess(code);
    catch "debug":
        lprint("debug session exited");
        lprint(PEDebug:-GetStatementCount(), "statements partially evaluated");
        return;
    catch:
        lprint(PEDebug:-GetStatementCount(), "statements partially evaluated before error");
        print(lastexception);
        error;
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
    gopts := 'gopts';
    kernelopts(opaquemodules=before);

    print(PEDebug:-GetStatementCount(), "statements processed. Success!");
    return res;    
end proc;

# runs the PE in debug mode
Debug := proc(p, opts:=PEOptions(), {num:=0})
    try
        if num > 0 then
            PEDebug:-RunThenStop(num);
        else
            PEDebug:-Begin();
        end if;
    catch "debug":
        lprint("debug session exited");
        return;
    end try;
    PartiallyEvaluate(p, opts);
end proc;

######################################################################################
# utility functions used by this package
######################################################################################

# caches M code of procedures so don't need to call ToM unneccesarily
getMCode := proc(fun) option cache;
    code, uniqueNames := M:-ToM(ToInert(fun));
    gen:-addNames(uniqueNames);
    code;
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
# Partial Evaluation of statements
############################################################################


# partially evaluates an arbitrary M statement
peM := proc(m::mform)
    h := Header(m);
    if assigned(pe[h]) then
        return pe[h](op(m));
    end if;
    error "(peM) not supported yet: %1", h;
end proc;


peResidualizeStatement := (f, e) -> f(ReduceExp(e));

#pe[MStandaloneExpr] := curry(peResidualizeStatement, MStandaloneExpr);
pe[MStandaloneExpr] := proc(e)
    MStandaloneExpr(ReduceExp(e));
end proc;

pe[MReturn] := curry(peResidualizeStatement, MReturn);
pe[MError]  := curry(peResidualizeStatement, MError);


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
            if Header(residual) = MTry and i < nargs then
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



pe[MAssign] := proc(n::mform({Local, GeneratedName, Name, AssignedName, Catenate}), expr::mform)
    # MCatenate is always global
    reduced := ReduceExp(expr);

    env := `if`(n::Global, genv, callStack:-topEnv());
    
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
    elif reduced::Both then
        env:-putVal(var, SVal(StaticPart(reduced)));
        MAssign(n, DynamicPart(reduced));
    elif reduced::Dynamic then
        env:-setValDynamic(var);
        MAssign(n, reduced);
    else
        error "(pe[MAssign]) unknown binding time";
    end if;
end proc;



pe[MTableAssign] := proc(tr::mform(Tableref), expr::mform)

    rindex := ReduceExp(IndexExp(tr));
    rexpr  := ReduceExp(expr);
    
    env := `if`(Var(tr)::Global, genv, callStack:-topEnv());
    
    # ToM will ensure that tableref will be a name
    var := Name(Var(tr));

    if [rindex,rexpr]::[Static,Static] then
        env:-putTblVal(var, SVal(rindex), SVal(rexpr));
        NULL;
        
    elif [rindex,rexpr]::[Static,Both] then
        env:-putTblVal(var, SVal(rindex), SVal(StaticPart(rexpr)));
        MTableAssign(subsop(2=rindex, tr), SVal(StaticPart(rexpr)));
        
    elif [rindex,rexpr]::[Static,Dynamic] then
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
        setVal := proc(x)
            if assigned(loopVarName) then
                env:-putVal(loopVarName, x, 'readonly');
            end if;
        end proc;
        unrollOnce := proc() # pass in the loop index
            res := peM(statseq);
            if res <> NULL then
                q:-enqueue(res);
            end if;        
        end proc;       
        result := () -> MStatSeq(qtoseq(q));        
    end module;
end proc;


#pe[MForFrom] := proc(loopVar::mform({Local, ExpSeq}), fromExp, byExp, toExp, statseq)
#    rFromExp := ReduceExp(fromExp);
#    rByExp   := ReduceExp(byExp);
#    rToExp   := ReduceExp(toExp);
#    
#    if [rFromExp,rByExp,rToExp]::[Static,Static,Static] then #unroll loop        
#        rFromExp := SVal(rFromExp);
#        rByExp := SVal(rByExp);
#        rToExp := SVal(rToExp);
#        
#        unroller := StaticLoopUnroller(loopVar, statseq);
#        for i from rFromExp by rByExp to rToExp do
#            unroller:-unrollOnce(i);
#        end do;        
#        unroller:-result();
#    else
#        error "dynamic loops not supported yet";
#    end if;
#end proc;

# TODO: rewrinte
pe[MForIn] := proc(loopVar, inExp, statseq)
    pe[MWhileForIn](loopVar, inExp, true, statseq);
end proc;


pe[MWhileForIn] := proc(loopVar, inExp, whileExp, statseq)
    rInExp := ReduceExp(inExp);
    if [rInExp]::list(Static) then
        unroller := StaticLoopUnroller(loopVar, statseq);
        for i in SVal(rInExp) do
            unroller:-setVal(i);
            rWhileExp := ReduceExp(whileExp);
            if rWhileExp::Or(Dynamic,Both) then
                error "dynamic while condition not supported: %1", rWhileExp;
            end if;
            if not SVal(rWhileExp) then break end if;
            unroller:-unrollOnce();
        end do;
        return unroller:-result();
    else
        error "dynamic loops not supported yet";
    end if;
end proc;


pe[MForFrom] := proc(loopVar, fromExp, byExp, toExp, statseq)
    pe[MWhileForFrom](loopVar, fromExp, byExp, toExp, true, statseq);
end proc;

pe[MWhileForFrom] := proc(loopVar, fromExp, byExp, toExp, whileExp, statseq)
    rFromExp  := ReduceExp(fromExp);
    rByExp    := ReduceExp(byExp);
    rToExp    := ReduceExp(toExp);    
    
    if [rFromExp,rByExp,rToExp]::list(Static) then #unroll loop        
        unroller := StaticLoopUnroller(loopVar, statseq);
        
        for i from SVal(rFromExp) by SVal(rByExp) to SVal(rToExp) do
            unroller:-setVal(i);
            rWhileExp := ReduceExp(whileExp);
            if rWhileExp::Or(Dynamic,Both) then
                error "dynamic while condition not supported: %1", rWhileExp;
            end if;
            if not SVal(rWhileExp) then break end if;
            unroller:-unrollOnce();
        end do;   
        unroller:-result();
    else
        print("rFromExp", rFromExp);
        print("rByExp", rByExp);
        print("rToExp", rToExp);
        error "dynamic loops not supported yet";
    end if;
end proc;

pe[MWhile] := proc()
    error "While loops are not supported";
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


##########################################################################################
# Statements that have function calls inside them
##########################################################################################


pe[MStandaloneFunction] := proc(var)
    unfold := proc(residualProcedure, redCall, fullCall)
        Unfold:-UnfoldStandalone(residualProcedure, redCall, fullCall, gen);
        #flattened := M:-FlattenStatSeq(res);
        #if nops(flattened) = 1 and op([1,0], flattened) = MStandaloneExpr then
        #    NULL
        #else
        #    flattened;
        #end if;
    end proc;
    residualize := proc()
        MStandaloneFunction(args);
    end proc;
    symbolic := proc()
        MStandaloneExpr(args);
    end proc;
    
    peFunction(args, unfold, residualize, symbolic);
end proc;



pe[MAssignToFunction] := proc(var::mform({Local, SingleUse}), funcCall::mform(Function))
    unfold := proc(residualProcedure, redCall, fullCall)
        res := Unfold:-UnfoldIntoAssign(residualProcedure, redCall, fullCall, gen, var);
        #flattened := M:-FlattenStatSeq(res);
        flattened := M:-RemoveUselessStandaloneExprs(res);
        if nops(flattened) = 1 and op([1,0], flattened) = MSingleAssign then
            assign := op(flattened);
            expr := op(2, assign);
            if expr::Static then
                callStack:-topEnv():-putVal(op(var), SVal(expr));
                return NULL;
            elif expr::Both then
                callStack:-topEnv():-putVal(op(var), SVal(StaticPart(expr)));
            end if;
        end if;
        flattened;
    end proc;

    residualize := proc()
        callStack:-topEnv():-setValDynamic(Name(var));
        MAssignToFunction(var, MFunction(args));
    end proc;

    # TODO, symbolic is bad name, change to something that has to do with static
    symbolic := proc(s)
        callStack:-topEnv():-putVal(Name(var), SVal(s));
        NULL;
    end proc;

    peFunction(op(funcCall), unfold, residualize, symbolic);
end proc;

###########################################################################################
# Partial Evaluation of function calls
###########################################################################################


# used to statically evaluate a type assertion on a parameter
checkParameterTypeAssertion := proc(value, paramSpec::mform(ParamSpec))
    ta := TypeAssertion(paramSpec);
    pass := `if`(nops(ta) > 0, type(value, op(ta)), true);
    `if`(pass, value, getParameterDefault(paramSpec));
end proc;

# returns a parameter's default value
getParameterDefault := proc(paramSpec::mform(ParamSpec))
    default := Default(paramSpec);
    if nops(default) > 0 then
        value := ReduceExp(op(default));
        if nops(value) <> 1 then
            error "expression sequence as default parameter value is not supported";
        elif value::Static then
            return op(newValue);
        else
            error "dynamic default values are not supported"
        end if;
    else
        error "static type assertion has failed, expected type %1 but received %2", 
              TypeAssertion(paramSpec), value;
    end if;
end proc;


isPossibleExpSeq := proc(exp::Dynamic)
    # returns true if a dynamic argument could possibly be an expression sequence
    gopts:-getConsiderExpseq() and Header(exp) <> MParam
end proc;


# returns an environment where static parameters are mapped to their static values
# as well as the static calls that will be residualized if the function is not unfolded
peArgList := proc(paramSeq::mform(ParamSeq), keywords::mform(Keywords), argExpSeq::mform(ExpSeq))
    env := OnENV(); # new env for function call
   	fullCall := SimpleQueue(); # residual function call including statics
   	redCall  := SimpleQueue(); # residual function call without statics
   	argsTbl := table(); # mappings for args
   	
   	numParams := nops(paramSeq);
   	possibleExpSeqSeen := false;
   	# table that remembers if an argument expression was a MEquation
   	equationArgs := {}; # set(integer)
   	toRemove := {}; # set of parameter names to be removed from the parameter sequence
    i := 1; 
    
   	# loop over expressions in function call
   	for arg in argExpSeq do
   	    reduced := ReduceExp(arg);
   	    if reduced::Both and nops(StaticPart(reduced)) <> 1 then
   	        error "cannot reliably match up parameters";
   	    end if;
   	    
   	    if reduced::Or(Static, Both) then
   	        # argument expression may have reduced to an expression sequence
   	        # flatten the way that Maple does
            staticPart := `if`(reduced::Both, StaticPart(reduced), reduced);
            
   	        for value in staticPart do
   	            toEnqueue := `if`(reduced::Both, DynamicPart(reduced), embed(value));
   	            fullCall:-enqueue(toEnqueue);
   	            if possibleExpSeqSeen or reduced::Both then
   	                redCall:-enqueue(toEnqueue);
   	            end if;
   	            if not possibleExpSeqSeen then 
   	                # we can still match up args to params
   	                # remember if this arg was coded directly as an equation
   	                equationArgs := equationArgs union `if`(Header(arg)=MEquation, {i}, {});
       	            if i <= numParams then
       	                paramSpec := op(i, paramSeq);
       	                value := checkParameterTypeAssertion(value, paramSpec);       
       	                env:-putVal(Name(paramSpec), value);
       	                toRemove := toRemove union `if`(reduced::Both, {}, {Name(paramSpec)});
       	            end if;
       	            argsTbl[i] := value; 
       	            i := i + 1;
       	        end if;
       	    end do;
       	    
   	    else # dynamic
   	        fullCall:-enqueue(reduced);
            redCall:-enqueue(reduced);
            if isPossibleExpSeq(reduced) then # i will not be used anymore if possibleExpSeqSeen is true
                possibleExpSeqSeen := true;
            else
                equationArgs := equationArgs union `if`(Header(arg)=MEquation, {i}, {});
                i := i + 1;
            end if; 	        
   	    end if;
   	end do;
   	
   	if possibleExpSeqSeen and nops(keywords) > 0 then
        error "the partial evaluator must be able to statically resolve all keyword arguments";
   	end if;
   	 
    if not possibleExpSeqSeen then
        env:-setNargs(i-1);
        # loop over arguments which are unmatched
        reducedArgs := fullCall:-toList();
        for i from numParams+1 to fullCall:-length() do
            if not member(i, equationArgs) then next end if;
            reducedArg := reducedArgs[i];
            if reducedArg::Static then
                eqn := SVal(reducedArg);                
                paramName := convert(lhs(eqn), string);            
                paramVal  := rhs(eqn);
                paramSpec := op(select(k -> Name(k) = paramName, keywords));
                if paramSpec <> NULL then
                    t := TypeAssertion(paramSpec);
                    if nops(t) > 0 and not type(paramVal, op(t)) then
                        #TODO, perhaps embed an error in the code?
                        error "invalid input: option `%1` expected to be of type %2, but received %3",
                              paramName, op(t), paramVal;
                    end if;
                    env:-putVal(paramName, paramVal);
                    toRemove := toRemove union {paramName};
                end if;
            else
                paramName := op([1,1], reducedArg);
                error "dynamic keyword equation arguments are not supported: %1", paramName;
            end if;        
        end do;
        
        # TODO, dynamic keyword equation arguments are not supported yet
        for paramSpec in keywords do
            if env:-isDynamic(Name(paramSpec)) then
                env:-putVal(Name(paramSpec), SVal(ReduceExp(op(Default(paramSpec)))));
            end if;
        end do
    end if;   
    
    env:-setArgs(argsTbl);
    f := MExpSeq @ qtoseq;
    
    # return results as a record just so its more organized
    Record('newEnv'=env, # environment mapping parameter names to static values
           'reducedCall'=f(redCall),  # the reduced call to be residualized if the proc is not unfolded
           'allCall'=f(fullCall), # the call but with static arguments still in their place
           'possibleExpSeq'=possibleExpSeqSeen,# true iff there is the possibility that one of the dynamic arguments could be and expression sequence
           'removeParams'=toRemove); # parameters to remove from the parameter sequence
end proc;


# Given an inert procedure and an inert function call to that procedure, decide if unfolding should be performed.
# probably won't be needed if I go with the sp-function approach
isUnfoldable := proc(inertProcedure::mform(Proc), argListInfo)
    # it dosen't matter if an argument is an expression sequence if there are no defined parameters
    if argListInfo:-possibleExpSeq and nops(Params(inertProcedure)) > 0 then
        return false;
    end if;
    
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


# takes continuations to be applied if f results in a procedure
peFunction := proc(funRef::Dynamic, 
                   argExpSeq::mform(ExpSeq), 
                   unfold::procedure, 
                   residualize::procedure, 
                   symbolic::procedure)
    local sfun;
    PEDebug:-FunctionStart(funRef);
    
    #print("funRef", funRef);
    
    fun := ReduceExp(funRef);

    if fun::Dynamic then
        # don't know what function was called, residualize call
        res := residualize(fun, ReduceExp(argExpSeq));
        PEDebug:-FunctionEnd();
        return res;
    end if; 
    
    sfun := SVal(fun);
    
    if type(eval(sfun), `procedure`) and not ormap(hasOption, ['builtin','pe_thunk'], eval(sfun)) then
        # if the procedure is builtin then do what the else clause does
        newName := gen(cat(op(1,funRef),"_"));
        peFunction_StaticFunction(funRef, eval(sfun), argExpSeq, newName, unfold, residualize, symbolic);
        
	elif type(sfun, `module`) then
	    if member(convert("ModuleApply",name), sfun) then
	        ma := sfun:-ModuleApply;
	    else
            ma := op(select(x->evalb(convert(x,string)="ModuleApply"), [op(3,eval(sfun))]));
            if ma = NULL then error "package does not contain ModuleApply" end if;
        end if;
	    peFunction_StaticFunction(funRef, ma, argExpSeq, gen("ma"), unfold, residualize, symbolic);
	    
    else
        redargs := ReduceExp(argExpSeq);
        if [redargs]::list(Static) then
            symbolic(embed( apply(sfun, SVal(redargs)) ));
        else
            residualize(fun, MExpSeq(redargs));
        end if;
    end if;
end proc;



# partial evaluation of a known procedure, when the function is static
peFunction_StaticFunction := proc(funRef::Dynamic, 
                                  fun::procedure, 
                                  argExpSeq::mform(ExpSeq), 
                                  newName, unfold, residualize, symbolic)
    if gopts:-hasFuncOpt(fun) then
        funOption := gopts:-funcOpt(fun);
        rcall := ReduceExp(argExpSeq);
        
        s := () -> (symbolic @ embed @ fun @ SVal)(rcall);
        r := () -> residualize(funRef, rcall);
        
        # if the function should be treated as PURE
        if funOption = PURE then
            `if`(rcall::Static, s(), peFunction_SpecializeThenDecideToUnfold(args[2..-1]))
        elif funOption = INTRINSIC then
            `if`(rcall::Static, s(), r())
        elif funOption = DYNAMIC then
            r()
        else
            error "unknown function option %1", funOption;
        end if;
    else
        peFunction_SpecializeThenDecideToUnfold(args[2..-1]);
    end if;
end proc;
 

# specialize the function
peFunction_SpecializeThenDecideToUnfold := proc(fun::procedure, argExpSeq::mform(ExpSeq), newName, unfold, residualize, symbolic)
	m := getMCode(eval(fun));

    argListInfo := peArgList(Params(m), Keywords(m), argExpSeq);

    callStack:-push(argListInfo:-newEnv);
    newProc := peFunction_GenerateNewSpecializedProc(m, newName, argListInfo);
    callStack:-pop();

    if isUnfoldable(newProc, argListInfo) then
        code[newName] := evaln(code[newName]); # remove mapping from code
        unfold(newProc, argListInfo:-reducedCall, argListInfo:-allCall);
    elif M:-UsesArgsOrNargs(newProc) then
        residualize(MString(newName), argListInfo:-allCall)
    else
        residualize(MString(newName), argListInfo:-reducedCall)
    end if;
end proc;


# takes inert code and assumes static variables are on top of callStack
# called before unfold
peFunction_GenerateNewSpecializedProc := proc(m::mform(Proc), n::string, argListInfo) :: mform(Proc);    
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

    # this doesn't need to be done for the goal function
    if nargs > 2 and not M:-UsesArgsOrNargs(newProc) then
        # This needs to be here because SetArgsFlags is called after partial evaluation of body of proc
        #p := x -> env:-isDynamic(Name(x));
        p := x -> member(Name(x), argListInfo:-removeParams);
        newParams   := remove(p, Params(m));
        newKeywords := remove(p, Keywords(m));
        newProc := subsop(1=newParams, 11=newKeywords, newProc);
    end if;

    code[n] := newProc;
    newProc;
end proc;


########################################################################################



end use
end module:
