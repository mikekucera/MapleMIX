# Simple online partial evaluator for a subset of maple

OnPE := module() option package;

description 
    "online partial evaluator for a subset of Maple";
export 
    ModuleApply, PartiallyEvaluate, Debug;
local 
$include "access_header.mpl"
    CallStack, PEDebug, Lifter, BuildModule, OnENV, 
    ReduceExp, Unfold,
    getMCode, embed, getEnv,
    pe, peM, peResidualizeStatement, peIF,
    StaticLoopUnroller,
    checkParameterTypeAssertion, getParameterDefault, 
    isPossibleExpSeq, peArgList, isUnfoldable,
    peFunction, peFunction_StaticFunction, 
    peFunction_SpecializeThenDecideToUnfold, 
    peFunction_GenerateNewSpecializedProc,  
    analyzeDynamicLoopBody, getCallSignature,
    
    # module local variables
    callStack,         # callStack grows by one OnENV for every function specialization
    specializedProcs,  # will change
    gen,               # used to generate new names
    genv,              # global environment
    gopts,             # options
    share              # table used to share functions
    ;


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
    local before, m, inertModule, res;
    # need access to module locals
    before := kernelopts(opaquemodules=false);
    
    # set up module locals
    gopts := opts;
    gen := NameGenerator();
    callStack := CallStack();
    specializedProcs := table();
    genv := OnENV(); # the global environment
    share := table();
    
    userinfo(1, PE, "PE on ", eval(p));
    m := getMCode(eval(p));
    userinfo(3, PE, "Successfully got MCode for", p);
    callStack:-push();
    
    try
        specializedProcs["ModuleApply"] := peFunction_GenerateNewSpecializedProc(m, "ModuleApply");
        Lifter:-LiftPostProcess(specializedProcs);
    catch "debug":
        lprint("debug session exited");
        lprint(PEDebug:-GetStatementCount(), "statements partially evaluated");
        return;
    catch "hard stop":
        lprint("hard stop caused by stop command");
        lprint(PEDebug:-GetStatementCount(), "statements partially evaluated");
        return;
# let the error go to the top as it makes debugging easier!
#    catch:
#        lprint(PEDebug:-GetStatementCount(), "statements partially evaluated before error");
#        print(lastexception);
#        error;
        #return copy(specializedProcs);
    end try;

    try
        inertModule := BuildModule("ModuleApply", specializedProcs);
    catch:
        lprint("conversion to inert module failed", lastexception);
        return copy(specializedProcs);
    end try;
    
    try
        res := eval(FromInert(inertModule));
    catch:
        lprint("FromInert on inertModule failed", lastexception);
        return copy(specializedProcs);
    end try;

    # unassign module locals
    gen := 'gen';
    specializedProcs := 'specializedProcs';
    genv := 'genv';
    callStack := 'callStack';
    gopts := 'gopts';
    share := 'share';
    
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
    local code, uniqueNames;
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

getEnv := proc(var::mname)
    `if`(var::Local, callStack:-topEnv(), genv)
end proc;

############################################################################
# Partial Evaluation of statements
############################################################################


# partially evaluates an arbitrary M statement
peM := proc(m::mform) local h;
    h := Header(m);
    userinfo(10, PE, "PE on an", h);
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
    local q, i, h, stmt, residual, statseq, size, stmtsAfterIf;
    
    statseq := M:-FlattenStatSeq(MStatSeq(args));
    size := nops(statseq);
    
    q := SimpleQueue();
    
    for i from 1 to size do
        stmt := op(i, statseq);
        h := Header(stmt);

        PEDebug:-StatementStart(stmt);
        
        if h = MIfThenElse then
            stmtsAfterIf := MStatSeq(op(i+1..size, statseq));
            q:-enqueue(peIF(stmt, stmtsAfterIf));
            PEDebug:-StatementEnd();
            break;
        end if;
        residual := peM(stmt);
        
        PEDebug:-StatementEnd(residual);

        if residual <> NULL then
            if Header(residual) = MTry and i < size then
                error "code after a try/catch is not supported";
            end if;
            q:-enqueue(residual);
            if M:-EndsWithErrorOrReturn(residual) then
                break
            end if;
        end if;
    end do;
    M:-RemoveUselessStandaloneExprs(MStatSeq(qtoseq(q)));
end proc;


pe[MCommand] := proc(command)
    if gopts:-getIgnoreCommands() then
        return NULL;
    end if;

    if command = "display" then
        callStack:-topEnv():-display();
    elif command = "displaynames" then
        callStack:-topEnv():-displayNames();
    elif command = "print" then
        print(op(2..-1, [args]));
    elif command = "lprint" then
        lprint(op(2..-1, [args]));
    elif command = "stop" then
        error "hard stop";
    else
        error "unknown command: %1", command;
    end if;
    NULL;
end proc;


peIF := proc(ifstat::mform(IfThenElse), S::mform(StatSeq))
    local rcond, env, C1, C2, S1, S2, prevTopLocal, prevTopGlobal, stopAfterC1, stopAfterC2, result;
    rcond := ReduceExp(Cond(ifstat));
    if rcond::Static then
        peM(MStatSeq(ssop(`if`(SVal(rcond), Then, Else)(ifstat)), ssop(S)));
    else
        # print("peIF", args);
        callStack:-setConditional();
        env := callStack:-topEnv();
        env:-grow();
        genv:-grow();

        C1 := peM(Then(ifstat));

        prevTopLocal, prevTopGlobal  := env:-markTop(), genv:-markTop();

        stopAfterC1 := M:-EndsWithErrorOrReturn(C1);
        # print("stopAfterC1", C1, stopAfterC1);
        if not stopAfterC1 then
            S1 := peM(S);
        end if;
        
        env:-shrinkGrow();
        genv:-shrinkGrow();

        C2 := peM(Else(ifstat));
        stopAfterC2 := M:-EndsWithErrorOrReturn(C2);
        
        if stopAfterC1 and stopAfterC2 then
            result := MIfThenElse(rcond, C1, C2);
        elif env:-equalsTop(prevTopLocal) and genv:-equalsTop(prevTopGlobal) then
            S1 := `if`(stopAfterC1, peM(S), S1);
            result := MStatSeq(MIfThenElse(rcond, C1, C2), ssop(S1));
        else
            S1 := `if`(stopAfterC1, MStatSeq(), S1);
            S2 := `if`(stopAfterC2, MStatSeq(), peM(S));
            result := MIfThenElse(rcond, MStatSeq(ssop(C1), ssop(S1)), MStatSeq(ssop(C2), ssop(S2)));
        end if;
        
        env:-shrink();
        genv:-shrink();
        result;
    end if
end proc;



pe[MAssign] := proc(n::mname, expr::mform)
    local reduced, env, var, shouldResidualize;
    userinfo(8, PE, "MAssign:", expr);
    env := getEnv(n);
    
    if Header(n) = MCatenate then
        var := ReduceExp(n);
        if var::Dynamic then
            return MAssign(n, ReduceExp(expr)); # TODO, maybe don't use n
        elif nops([SVal(var)]) <> 1 then
            error "multiple assignment not supported"
        else
            var := convert(SVal(var), string);
        end if
    else
        var := Name(n);
    end if;
    
    # not using end configuration stores, therefore if the global env has been 
    # updated then a function won't be shared
    # TODO, make sure this is true
    if n::Global then # very conservative
        callStack:-setGlobalEnvUpdated(true);
    end if;
        
    # id assign is of the form (name := name) then reduction isn't necessary
    if expr::envname then
        shouldResidualize := env:-bind(expr, 'newName'=var);
        `if`(shouldResidualize, MAssign(n, expr), NULL);
    else
        reduced := ReduceExp(expr);
        if reduced::Static then
            env:-putVal(var, SVal(reduced));
            NULL;
        elif reduced::Dynamic then
            env:-setValDynamic(var);
            MAssign(n, reduced);
        else # Both
            env:-putVal(var, SVal(StaticPart(reduced)));
            MAssign(n, DynamicPart(reduced));
        end if;
    end if;
end proc;


 
pe[MAssignToTable] := proc(n::mname, expr::mform(Tableref)) local tblVar, rindex, env;
    rindex := ReduceExp(IndexExp(expr));
    tblVar := Var(expr);
    env := getEnv(tblVar);
    
    if not env:-isTblValAssigned(Name(tblVar), SVal(rindex)) then
        env:-putTblVal(Name(tblVar), SVal(rindex), table());
    end if;
    
    pe[MAssign](n, expr); # TODO, this would have to change if PE was run as a fixed point
end proc;


pe[MAssignTableIndex] := proc(tr::mform(Tableref), expr::mform)
    local rindex, rexpr, env, var;
    rindex := ReduceExp(IndexExp(tr));
    rexpr  := ReduceExp(expr);
    env := getEnv(Var(tr));
    var := Name(Var(tr)); # ToM will ensure that tableref will be a name

    if Var(tr)::Global then # very conservative
        callStack:-setGlobalEnvUpdated(true);
    end if;
    
    if [rindex,rexpr]::[Static,Static] then
userinfo(5, PE, "Static -- putting into env", SVal(rexpr));
        env:-putTblVal(var, SVal(rindex), SVal(rexpr));
        NULL;
        
    elif [rindex,rexpr]::[Static,Both] then
userinfo(5, PE, "Both -- putting into env", SVal(StaticPart(rexpr)));
        env:-putTblVal(var, SVal(rindex), SVal(StaticPart(rexpr)));
        MAssignTableIndex(subsop(2=rindex, tr), SVal(StaticPart(rexpr)));
        
    elif [rindex,rexpr]::[Static,Dynamic] then
        env:-setTblValDynamic(var, SVal(rindex));
        MAssignTableIndex(subsop(2=rindex, tr), rexpr);
        
    else
        env:-setValDynamic(var);
        MAssignTableIndex(subsop(2=rindex, tr), rexpr);
    end if;
end proc;


# returns an object that can be used to unroll the body of a loop
StaticLoopUnroller := proc(loopVar, statseq) :: `module`;
    local env, loopVarName, q;
    env := callStack:-topEnv();
    if loopVar <> MExpSeq() then
        loopVarName := Name(loopVar);
        env:-setLoopVar(loopVarName);
    end if;
    
    q := SimpleQueue();
    
    return module() export setVal, unrollOnce, result;
        setVal := proc(x)
            if assigned(loopVarName) then
                env:-putLoopVarVal(loopVarName, x);
            end if;
        end proc;
        unrollOnce := proc() local res; # pass in the loop index
            res := peM(statseq);
            if res <> NULL then
                q:-enqueue(res);
            end if;        
        end proc;       
        result := () -> MStatSeq(qtoseq(q));        
    end module;
end proc;


# very conservative approach to dynamic loops
# will simply residualize the entire loop, but must analyze to determine
# variables that have become dynamic
analyzeDynamicLoopBody := proc(body::mform)
    local notImplemented, readVar, readLocal, readGlobal, readTableref, writeVar, writeTable;
    notImplemented := () -> ERROR("non-intrinsic call in dynamic loop not supported");
    #readVar := proc(n::string, env)
        #if env:-isStatic(n) then
        #    error "static value in dynamic loop body is not supported yet";
        #end if;
    #end proc;
    #readLocal  := n -> readVar(n, callStack:-topEnv());
    #readGlobal := n -> readVar(n, genv);
    readTableref := proc(var)
        if not getEnv(var):-isDynamic(Name(var)) then # the entire table must be dynamic
            error "possibly static table lookup in dynamic loop, not supported yet";
        end if;
    end proc;
    writeVar   := proc(var)
        if getEnv(var):-isStatic(Name(var)) then
            error "static -> dynamic is not allowed";
        end if;
    end proc;
    writeTable := tblref -> writeVar(Var(tblref));
    
    eval(body, [#MAssignToFunction   = notImplemented,
                #MStandaloneFunction = notImplemented,
                MAssign = writeVar,
                MAssignToTable = writeVar,
                MAssignTableIndex = writeTable,
                MTableref = readTableref
                #MName = readGlobal,
                #MLocal = readLocal,
                #MParam = readLocal,
                #MGeneratedName = readLocal,
                #MSingleUse = readLocal 
                ]);    
    NULL
end proc;


pe[MForIn] := proc(loopVar, inExp, statseq)
    pe[MWhileForIn](loopVar, inExp, MStatic(true), statseq);
end proc;


pe[MWhileForIn] := proc(loopVar, inExp, whileExp, statseq)
    local rInExp, unroller, i, rWhileExp;
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
        # need to do this because unassigned locals are considered static
        getEnv(loopVar):-setValDynamic(Name(loopVar));
        analyzeDynamicLoopBody(statseq);
        analyzeDynamicLoopBody(whileExp);
        MWhileForIn(loopVar, rInExp, whileExp, peM(statseq));
    end if;
end proc;


pe[MForFrom] := proc(loopVar, fromExp, byExp, toExp, statseq)
    pe[MWhileForFrom](loopVar, fromExp, byExp, toExp, MStatic(true), statseq);
end proc;

pe[MWhileForFrom] := proc(loopVar, fromExp, byExp, toExp, whileExp, statseq)
    local rFromExp, rByExp, rToExp, unroller, i, rWhileExp;
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
        # need to do this because unassigned locals are considered static
        getEnv(loopVar):-setValDynamic(Name(loopVar));
        analyzeDynamicLoopBody(statseq);
        analyzeDynamicLoopBody(whileExp);
        MWhileForFrom(loopVar, rFromExp, rByExp, rToExp, whileExp, peM(statseq))
    end if;
end proc;

pe[MWhile] := proc()
    error "While loops are not supported";
end proc;

pe[MTry] := proc(tryBlock, catchSeq, finallyBlock)
    local rtry, stat, q, c, rcat, rfin;
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

    MTry(rtry, MCatchSeq(qtoseq(q)), rfin);
end proc;


##########################################################################################
# Statements that have function calls inside them
##########################################################################################


pe[MStandaloneFunction] := proc(var) local unfold;
    unfold := proc(residualProcedure, redCall, fullCall)
        Unfold:-UnfoldStandalone(residualProcedure, redCall, fullCall, gen);
    end proc;
    peFunction(args, unfold, () -> MStandaloneFunction(args), () -> MStandaloneExpr(args));
end proc;


# no support for assigning to a global variable, 
pe[MAssignToFunction] := proc(var::mform({Local, SingleUse}), funcCall::mform(Function))
    local unfold, residualize, symbolic;
    unfold := proc(residualProcedure, redCall, fullCall)
        local res, flattened, assign, expr;
        res := Unfold:-UnfoldIntoAssign(residualProcedure, redCall, fullCall, gen, var);
        #flattened := M:-FlattenStatSeq(res);
        flattened := M:-RemoveUselessStandaloneExprs(res);
        if nops(flattened) = 1 and op([1,0], flattened) = MSingleAssign then
            assign := op(flattened);
            expr := op(2, assign);
            if expr::Static then
userinfo(5, PE, "Static -- var := expr", Name(var), SVal(expr));
                callStack:-topEnv():-putVal(Name(var), SVal(expr));
                return NULL;
            elif expr::Both then
userinfo(5, PE, "Both -- var := expr", Name(var), SVal(StaticPart(expr)));
                callStack:-topEnv():-putVal(Name(var), SVal(StaticPart(expr)));
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
checkParameterTypeAssertion := proc(value::list(Static), paramSpec::mform(ParamSpec)) local ta;
    ta := TypeAssertion(paramSpec);
    `if`(nops(ta) > 0, type(value, list(op(ta))), true);
end proc;

# returns a parameter's default value
getParameterDefault := proc(paramSpec::mform(ParamSpec)) local default, value;
    default := Default(paramSpec);
    if nops(default) > 0 then
        value := ReduceExp(op(default));
        if nops(value) <> 1 then
            error "expression sequence as default parameter value is not supported";
        elif value::Static then
            return op(value);
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
    local env, fullCall, redCall, numParams, possibleExpSeqSeen, equationArgs, toRemove, i, t, f,
          reduced, staticPart, val, toEnqueue, paramName, paramVal, paramSpec, reducedArgs, eqn,
          reducedArg, arg, tmp, shouldResidualize;
          
    env := OnENV(); # new env for function call
    env:-setLink(callStack:-topEnv());
    
   	fullCall := SimpleQueue(); # residual function call including statics
   	redCall  := SimpleQueue(); # residual function call without statics
   	#argsTbl := table(); # mappings for args
   	
   	numParams := nops(paramSeq);
   	possibleExpSeqSeen := false;
   	# table that remembers if an argument expression was a MEquation
   	equationArgs := {}; # set(integer)
   	toRemove := {}; # set of parameter names to be removed from the parameter sequence
    i := 1; # value of i will not be used if possibleExpSeqSeen is true
    
   	# loop over expressions in function call
   	for arg in argExpSeq do
   	
   	    #if not possibleExpSeqSeen and arg::envname and getEnv(arg):-isStaticTable(Name(arg)) then
   	    #    paramName := `if`(i <= numParams, Name(op(i, paramSeq)), NULL);
   	    #    shouldResidualize := env:-bind(arg, 'environ'=getEnv(arg), 'newName'=paramName, 'argNum'=i);
   	    #    if true then #if shouldResidualize then
   	    #        print("redcall");
   	    #        redCall:-enqueue(arg);
   	    #        fullCall:-enqueue(arg);
   	    #    else
   	    #        toRemove := toRemove union {paramName};
   	    #        # ??? fullCall:-enqueue(???);
   	    #    end if;
   	    #    
   	    #    i := i + 1;
   	    #    next;
   	    #end if;
   	    
   	    reduced := ReduceExp(arg);
   	    if reduced::Both and nops(StaticPart(reduced)) <> 1 then
   	        error "cannot reliably match up parameters";
   	    end if;
   	    
   	    if reduced::Or(Static, Both) then
   	        # argument expression may have reduced to an expression sequence
   	        # flatten the way that Maple does
            staticPart := `if`(reduced::Both, StaticPart(reduced), reduced);
            
   	        for val in map(() -> [args], staticPart) do
   	            toEnqueue := `if`(reduced::Both, DynamicPart(reduced), embed(op(val)));
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
       	                if not checkParameterTypeAssertion(val, paramSpec) then
       	                    val := [getParameterDefault(paramSpec)];
       	                end if;
       	                env:-putVal(Name(paramSpec), op(val));#`if`(type(val,last_name_eval),eval(val),val));
       	                toRemove := toRemove union `if`(reduced::Both, {}, {Name(paramSpec)});
       	            end if;
       	            env:-putArgsVal(i, op(val));
       	            i := i + 1;
       	        end if;
       	    end do;
       	    
   	    else # dynamic
   	        fullCall:-enqueue(reduced);
            redCall:-enqueue(reduced);
            if isPossibleExpSeq(reduced) then
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
                tmp := SVal(ReduceExp(op(Default(paramSpec))));
                userinfo(5, PE, "doing putVal with", tmp, "which was", paramSpec);
                env:-putVal(Name(paramSpec), tmp);
            end if;
        end do
    end if;   
    
    #env:-setArgs(argsTbl);
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
isUnfoldable := proc(mProc::mform(Proc), argListInfo) local flattened;
    # it dosen't matter if an argument is an expression sequence if there are no defined parameters
    if argListInfo:-possibleExpSeq and nops(Params(mProc)) > 0 then
        return false;
    end if;
    
    if not callStack:-inConditional() then
        true;
    elif not hasfun(mProc, {MStandaloneFunction, MAssignToFunction}) then
        # in this case there is no recursive call so unfold
        true;
    else
        flattened := M:-FlattenStatSeq(ProcBody(mProc));
        # if all the func does is return a static value then there is no
        # reason not to unfold
        
        # if the body of the function is empty then go ahead and unfold
        if nops(flattened) = 0 then
            true
        else # if the function body consists of a single static than it can be easily unfolded
            nops(op([1,1], flattened)) = 1 
            and member(op([1,0], flattened), {MReturn, MStandaloneExpr})
            and op([1,1], flattened)::Static
        end if;
    end if;
end proc;


# takes continuations to be applied if f results in a procedure
peFunction := proc(funRef::Dynamic, 
                   argExpSeq::mform(ExpSeq), 
                   unfold::procedure, 
                   residualize::procedure, 
                   symbolic::procedure)
    local fun, sfun, newName, ma, redargs, res;
    PEDebug:-FunctionStart(funRef);
    userinfo(10, PE, "Reducing function call", funRef);
    
    fun := ReduceExp(funRef);

    if fun::Dynamic then
        # don't know what function was called, residualize call
        res := residualize(fun, ReduceExp(argExpSeq));
        PEDebug:-FunctionEnd();
        return res;
    end if; 
    
    sfun := SVal(fun);
    
    if type(sfun, `procedure`) and not ormap(hasOption, ['builtin','pe_thunk'], sfun) then
        # if the procedure is builtin then do what the else clause does
        newName := gen(cat(op(1,funRef),"_"));
        peFunction_StaticFunction(funRef, sfun, argExpSeq, newName, unfold, residualize, symbolic);
        
	elif type(sfun, `module`) then
	    if member(convert("ModuleApply",name), sfun) then
	        ma := sfun:-ModuleApply;
	    else
            # need the full eval, because we need to op into it
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
    local funOption, rcall, s, r, tmp;
    if gopts:-hasFuncOpt(fun) then
        funOption := gopts:-funcOpt(fun);
        userinfo(5, PE, "StaticFunction: About to reduce", argExpSeq);
        rcall := ReduceExp(argExpSeq);
        userinfo(5, PE, "StaticFunction: Arguments for call is", rcall);
        
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
 
# returns a list of the arguments used to specialize a procedure
# with the special value DYN substituted for dynamic arguments
getCallSignature := proc(argExpSeq::mform(ExpSeq))
    [op(map(x -> `if`(x::Dynamic, DYN, x), argExpSeq))];
end proc;

# specialize the function
peFunction_SpecializeThenDecideToUnfold := 
    proc(fun::procedure, argExpSeq::mform(ExpSeq), generatedName, unfold, residualize, symbolic)
    local m, argListInfo, newProc, newName, rec, signature, call;
    
	m := getMCode(eval(fun));
    newName := generatedName;
	
    argListInfo := peArgList(Params(m), Keywords(m), argExpSeq);
    signature := fun, getCallSignature(argListInfo:-allCall);
    
    # handle sharing issues
    if not assigned(share[signature]) then
        rec := Record('code', 'procName', 'mustResid', 'finished');
        rec:-procName := newName;
        rec:-mustResid := false;
        rec:-finished  := false;
        share[signature] := rec;
        
        callStack:-push(argListInfo:-newEnv);
        # at this point rec:-finished is false
        newProc := peFunction_GenerateNewSpecializedProc(m, newName, argListInfo);
        # if the global env was altered then we do not allow sharing
        if callStack:-wasGlobalEnvUpdated() then 
            share[signature] := 'share[signature]';
        else
            rec:-code := newProc;
            rec:-finished := true;
        end if;
        callStack:-pop();
    else
        rec := share[signature];
        if not rec:-finished then # then this is a recursive call to a function currently being specialized
            rec:-mustResid := true;
            # TODO, is it safe to just use reducedCall?
            return residualize(MString(rec:-procName), argListInfo:-reducedCall)
        end if;
        newProc := rec:-code;
        newName := rec:-procName;
    end if;
    
    if not rec:-mustResid and isUnfoldable(newProc, argListInfo) then
        unfold(newProc, argListInfo:-reducedCall, argListInfo:-allCall);
    else
        specializedProcs[newName] := newProc;
        call := `if`(M:-UsesArgsOrNargs(newProc), argListInfo:-allCall, argListInfo:-reducedCall);
        residualize(MString(newName), call)
    end if;
end proc;


# takes inert specializedProcs and assumes static variables are on top of callStack
# called before unfold
peFunction_GenerateNewSpecializedProc := proc(m::mform(Proc), n::string, argListInfo) :: mform(Proc);
    local env, lexMap, loc, varName, body, newProc, p, newParams, newKeywords;
    # attach lexical environment
    env := callStack:-topEnv();
    if not env:-hasLex() then
        lexMap := M:-CreateLexNameMap(LexSeq(m), curry(op,2));
        env:-attachLex(lexMap);
    end if;
    
    # create static locals
    for loc in Locals(m) do
        varName := Var(loc);
        env:-putVal(varName, convert(varName, '`local`'));
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

    #specializedProcs[n] := newProc;
    newProc;
end proc;


########################################################################################



end use
end module:
