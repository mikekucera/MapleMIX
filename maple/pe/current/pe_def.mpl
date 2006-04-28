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
    getMCode, getMCodeFromCache, embed, getEnv,
    pe, peM, peResidualizeStatement, peIF,
    StaticLoopUnroller,
    checkParameterTypeAssertion, getParameterDefault,
    isPossibleExpSeq, peArgList, isUnfoldable,
    peFunction, peFunction_StaticFunction,
    peFunction_SpecializeThenDecideToUnfold,
    peFunction_GenerateNewSpecializedProc,
    analyzeDynamicLoopBody, getCallSignature,
    replaceLocalsWithNewParams,
    extractBindingFromEquationConditional, extractBinding,
    handleStaticLoop, handleDynamicLoop, forFromTerminationTest, insertDriver,

    # module local variables
    callStack,         # callStack grows by one OnENV for every function specialization
    specializedProcs,  # code for procedures that don't get unfolded
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
        ##Lifter:-LiftPostProcess(specializedProcs);
        ##specializedProcs;
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

getMCodeFromCache := proc(fun) option cache;
    local code, uniqueNames;
    code, uniqueNames := M:-ToM(ToInert(fun));
    gen:-addNames(uniqueNames);
    code;
end proc;

getMCode := proc(fun)
    M:-TransformIf:-TransformToDAG(getMCodeFromCache(fun));
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


peM := proc(m::mform) local h;
    if nargs = 0 then
        return NULL;
    end if;
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
    local q, i, j, h, stmt, residual, statseq, size, stmtsAfterIf, below;

    statseq := M:-FlattenStatSeq(MStatSeq(args));
    size := nops(statseq);

    q := SimpleQueue();

    for i from 1 to size do
        stmt := op(i, statseq);
        h := Header(stmt);

        PEDebug:-StatementStart(stmt);

        if member(h, {MWhileForFrom, MWhileForIn}) then
            below := MStatSeq(op(i+1..size, statseq));
            residual := pe[h](op(stmt), below);
            if residual <> NULL then q:-enqueue( residual ); end if;
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

pe[MRef] := proc(ref)
    peM(ref:-code); # this means the partial evaluator removes all references
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




extractBindingFromEquationConditional := proc(rcond, {neg:=false})
    extractBinding(rcond, `if`(neg, MInequat, MEquation));
end proc;

extractBinding := proc(rcond, equattype)
    if typematch(rcond, equattype('n'::mname, 'v'::Static)) then
        getEnv(n):-put(Name(n), SVal(v));
    elif typematch(rcond, equattype(MTableref('n'::mname, 'i'::Static), 'v'::Static)) then
        getEnv(n):-putTblVal(Name(n), i, SVal(v));
    end if;
end proc;


pe[MIfThenElse] := proc(cond, thenBranch, elseBranch)
    local rcond, env, C1, C2, S, S1, S2, prevTopLocal, prevTopGlobal,
          stopAfterC1, stopAfterC2, result, a1, a2, a3, a4;
    rcond := ReduceExp(cond);
    if rcond::Static then
        peM(`if`(SVal(rcond), thenBranch, elseBranch));
    else
        env := callStack:-topEnv();
        env:-grow();
        genv:-grow();

        # extract data from conditional expression
        extractBindingFromEquationConditional(rcond, neg=false);

        C1 := peM(CodeUpToPointer(thenBranch));

        stopAfterC1 := M:-EndsWithErrorOrReturn(C1);
        S := CodeBelow(thenBranch);

        if not stopAfterC1 then
            # grow the stack again for S1
            env:-grow();
            genv:-grow();
            S1 := peM(S);
            # pop the effects of S1, don't save
            env:-pop();
            genv:-pop();
        end if;

        # pop the effects of C1 and save
        prevTopLocal := env:-pop();
        prevTopGlobal := genv:-pop();
        # grow again for C2
        env:-grow();
        genv:-grow();

        extractBindingFromEquationConditional(rcond, neg=true);

        C2 := peM(CodeUpToPointer(elseBranch));
        S := CodeBelow(elseBranch);

        stopAfterC2 := M:-EndsWithErrorOrReturn(C2); # TODO, should not be needed

        if stopAfterC1 and stopAfterC2 then
            result := MIfThenElse(rcond, C1, C2);
        elif (not ormap(rcurry(hasfun, MIfThenElse), [C1, C2])) and
            env:-equalsTop(prevTopLocal) and genv:-equalsTop(prevTopGlobal) then
            S1 := `if`(stopAfterC1, peM(S), S1);
            result := MStatSeq(MIfThenElse(rcond, C1, C2), ssop(S1));
        else
            S1 := `if`(stopAfterC1, MStatSeq(), S1);
            S2 := `if`(stopAfterC2, MStatSeq(), peM(S));
            # TODO, get rid of merging
            #a1, a2 := env:-merge(prevTopLocal);
            #a3, a4 := genv:-merge(prevTopGlobal);
            #result := MIfThenElse(rcond, MStatSeq(ssop(C1), ssop(S1), ssop(a1), ssop(a3)),
            #                             MStatSeq(ssop(C2), ssop(S2), ssop(a2), ssop(a4)));
            result := MIfThenElse(rcond, MStatSeq(ssop(C1), ssop(S1)), MStatSeq(ssop(C2), ssop(S2)));
        end if;
        env:-pop();
        genv:-pop();
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

    reduced := ReduceExp(expr);

    if reduced::Static then
        env:-put(var, SVal(reduced));
        NULL;
    elif reduced::Dynamic then
        env:-put(var, reduced);
        #env:-setValDynamic(var);
        MAssign(n, reduced);
    else # Both
        env:-put(var, SVal(StaticPart(reduced)));
        MAssign(n, DynamicPart(reduced));
    end if;

end proc;



pe[MAssignToTable] := proc(n::mname, expr::mform(Tableref)) local tblVar, rindex, env;
    rindex := ReduceExp(IndexExp(expr));
    tblVar := Var(expr);
    env := getEnv(tblVar);

    if not env:-isTblValAssigned(Name(tblVar), rindex) then
        env:-putTblVal(Name(tblVar), rindex, table());
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
        env:-putTblVal(var, rindex, SVal(rexpr));
        NULL;

    elif [rindex,rexpr]::[Static,Both] then
        env:-putTblVal(var, rindex, SVal(StaticPart(rexpr)));
        MAssignTableIndex(subsop(2=rindex, tr), SVal(StaticPart(rexpr)));

    elif [rindex,rexpr]::[Static,Dynamic] then
        env:-setTblValDynamic(var, rindex);
        MAssignTableIndex(subsop(2=rindex, tr), rexpr);

    else
        env:-setValDynamic(var);
        MAssignTableIndex(subsop(2=rindex, tr), rexpr);
    end if;
end proc;





# very conservative approach to dynamic loops
# will simply residualize the entire loop, but must analyze to determine
# variables that have become dynamic
analyzeDynamicLoopBody := proc(body::mform)
    local notImplemented, readVar, readLocal, readGlobal, readTableref, writeVar, writeTable, q;

    q := SimpleQueue();

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
    writeVar := proc(var) local env, n;
        n := Name(var);
        env := callStack:-topEnv();
        if env:-isStatic(n) then # cant be assignments to parameters anyways
            q:-enqueue(MAssign(MLocal(n), embed(env:-get(n))));
            env:-setValDynamic(n);
        elif genv:-isStatic(n) then # just make it a name
            q:-enqueue(MAssign(MName(n), embed(genv:-get(n))));
            env:-setValDynamic(n);
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

    qtoseq(q);
end proc;

# returns an object that can be used to unroll the body of a loop
#StaticLoopUnroller := proc(loopVar, statseq, whileExp) :: `module`;
#    local env, loopVarName, q;
#    env := callStack:-topEnv();
#    if loopVar <> MExpSeq() then
#        loopVarName := Name(loopVar);
#        env:-setLoopVar(loopVarName);
#    end if;#
#
#    q := SimpleQueue();
#
#    return module()
#        local lastStmt;
#        export setVal, unrollOnce, result, isLastStmtReturn;
#
#        unrollOnce := proc(loopVarVal) local rWhileExp, res; # pass in the loop index
#            # set the loop variable if it exists
#            if assigned(loopVarName) then
#                env:-put(loopVarName, msop(loopVarVal), 'loopVarSet'=true);
#            end if;
#            # reduce the while condition, it can't be dynamic
#            rWhileExp := ReduceExp(whileExp);
#            if rWhileExp::Or(Dynamic,Both) then
#                error "dynamic while condition not supported: %1", rWhileExp;
#            end if;
#            # check the while condition
#            if not SVal(rWhileExp) then
#                return false;
#            end if;
#            # unroll loop once
#            lastStmt := peM(statseq);
#            if lastStmt <> NULL then
#                q:-enqueue(lastStmt);
#            end if;
#            # stop if it ends with a return
#            if assigned(lastStmt) and Header(op(-1, lastStmt)) = MReturn then
#                return false
#            end if;
#            return true;
#        end proc;
#
#        result := () -> MStatSeq(qtoseq(q));
#    end module;
#end proc;


#pe[MWhileForIn] := proc(loopVar, inExp, whileExp, statseq)
#    local rInExp, rWhileExp, assigns, stmt, unroll;
#    rInExp := ReduceExp(inExp);
#
#    unroll := proc(expr) local unroller, i;
#        unroller := StaticLoopUnroller(loopVar, statseq, whileExp);
#        for i in expr do
#            if not unroller:-unrollOnce(i) then break end if;
#        end do;
#        return unroller:-result();
#    end proc;
#
#    if [rInExp]::list(Static) or Header(rInExp) = MList then
#        unroll(op(rInExp));
#    #elif Header(rInExp) = MSubst and Header(DynExpr(rInExp)) = MList then
#    #    unroll(op(DynExpr(rInExp)));
#    else
#        # need to do this because unassigned locals are considered static
#        getEnv(loopVar):-setValDynamic(Name(loopVar));
#        assigns := op(map(analyzeDynamicLoopBody, [statseq, whileExp]));
#        stmt := MWhileForIn(loopVar, rInExp, whileExp, peM(statseq));
#        `if`(nops([assigns]) > 0, MStatSeq(assigns, stmt), stmt);
#    end if;
#end proc;



pe[MWhileForIn] := proc(loopVar, inExp, whileExp, statseq, below)
    local rInExp, env, indexVar, mkDriver, mkDynamicLoop;
    rInExp := ReduceExp(inExp);

    if rInExp::Static then
        if nops(rInExp) > 0 then
            indexVar := gen("indexVar");
            env := callStack:-topEnv();
            env:-setLoopVar(Name(loopVar));
            env:-setLoopVar(indexVar, SVal(rInExp)); # TODO, this isn't needed
            env:-put(indexVar, 1, 'loopVarSet'=true);
            env:-put(Name(loopVar), op(1, SVal(rInExp)), 'loopVarSet'=true);

            mkDriver := thunk -> MForInDriver(thunk, below, loopVar, indexVar, rInExp, whileExp);
            handleStaticLoop(whileExp, statseq, mkDriver);
        else
            peM(below);
        end if;
    else
        mkDynamicLoop := () -> MWhileForIn(loopVar, rInExp, whileExp, peM(statseq));
        handleDynamicLoop(loopVar, statseq, whileExp, below, mkDynamicLoop);
    end if;
end proc;



pe[MWhileForFrom] := proc(loopVar, fromExp, byExp, toExp, whileExp, statseq, below)
    local rFromExp, rByExp, rToExp, env, mkDriver, mkDynamicLoop;
    rFromExp  := ReduceExp(fromExp);
    rByExp    := ReduceExp(byExp);
    rToExp    := ReduceExp(toExp);

    if [rFromExp,rByExp,rToExp]::list(Static) then #unroll loop
        if not forFromTerminationTest(rByExp, rToExp, SVal(rFromExp)) then
            env := callStack:-topEnv();
            env:-setLoopVar(Name(loopVar));
            env:-put(Name(loopVar), SVal(rFromExp), 'loopVarSet'=true);

            mkDriver := thunk -> MForFromDriver(thunk, below, loopVar, rByExp, rToExp, whileExp);
            handleStaticLoop(whileExp, statseq, mkDriver);
        else
            peM(below);
        end if
    else
        mkDynamicLoop := () -> MWhileForFrom(loopVar, rFromExp, rByExp, rToExp, whileExp, peM(statseq));
        handleDynamicLoop(loopVar, statseq, whileExp, below, mkDynamicLoop);
    end if;
end proc;


handleStaticLoop := proc(whileExp, statseq, mkDriver::procedure)
    local rWhileExp, thunk, driver;
    rWhileExp := ReduceExp(whileExp);
    if rWhileExp::Dynamic then
        error "dynamic while condition not supported";
    end if;
    if SVal(rWhileExp) then
        # crazy circular reference!
        thunk := () -> insertDriver(statseq, driver);
        driver := mkDriver(thunk);
        peM(thunk());
    else
        NULL
    end if;
end proc;


# follows all paths and inserts drivers at the end
insertDriver := proc(statseq::mform(StatSeq), driver::mform({ForFromDriver, ForInDriver}))
    local flattened, front, last;
    flattened := M:-FlattenStatSeq(statseq);
    if nops(flattened) = 0 then
        MStatSeq(driver);
    else
        front := Front(flattened);
        last  := Last(flattened);
        if Header(last) = MIfThenElse then
            MStatSeq(front, MIfThenElse(Cond(last),
                                        procname(Then(last), driver),
                                        procname(Else(last), driver) ))
        elif Header(last) = MRef then
            MStatSeq(front, MRef('code'=procname(op(last):-code, driver)))
        else
            MStatSeq(ssop(flattened), driver)
        end if;
    end if;
end proc;


handleDynamicLoop := proc(loopVar, statseq, whileExp, below, mkDynamicLoop)
    local assigns, stmt;
    # need to do this because unassigned locals are considered static
    getEnv(loopVar):-setValDynamic(Name(loopVar));
    assigns := op(map(analyzeDynamicLoopBody, [statseq, whileExp]));
    stmt := mkDynamicLoop();
    `if`(nops([assigns]) > 0, MStatSeq(assigns, stmt, peM(below)), MStatSeq(stmt, peM(below)));
end proc;


forFromTerminationTest := proc(byVal, toVal, val)
    (SVal(byVal) > 0 and val > SVal(toVal)) or
    (SVal(byVal) < 0 and val < SVal(toVal))
end proc;


pe[MForFromDriver] := proc(thunk, below, loopVar, byVal, toVal, whileExp)
    local env, val, rWhileExp;
    env := callStack:-topEnv();
    val::integer := env:-get(Name(loopVar)) + SVal(byVal);
    env:-put(Name(loopVar), val, 'loopVarSet'=true);

    if forFromTerminationTest(byVal, toVal, val) then
        peM(below);
    else

        rWhileExp := ReduceExp(whileExp);
        if rWhileExp::Dynamic then
            error "Dynamic while condition not supported";
        end if;
        `if`(SVal(rWhileExp), peM(thunk()), peM(below));
    end if
end proc;


pe[MForInDriver] := proc(thunk, below, loopVar, indexVar, rInExp, whileExp)
    local env, val, rWhileExp;
    env := callStack:-topEnv();
    val::integer := env:-get(indexVar) + 1;
    env:-put(indexVar, val, 'loopVarSet'=true);

    if val > nops(SVal(rInExp)) then
        peM(below);
    else
        env:-put(Name(loopVar), op(val, SVal(rInExp)), 'loopVarSet'=true);
        rWhileExp := ReduceExp(whileExp);
        if rWhileExp::Dynamic then
            error "Dynamic while condition not supported";
        end if;
        `if`(SVal(rWhileExp), peM(thunk()), peM(below));
    end if
end proc;

#pe[MWhileForFrom] := proc(loopVar, fromExp, byExp, toExp, whileExp, statseq)
#    local rFromExp, rByExp, rToExp, unroller, i, rWhileExp, assigns, stmt;
#    rFromExp  := ReduceExp(fromExp);
#    rByExp    := ReduceExp(byExp);
#    rToExp    := ReduceExp(toExp);
#
#    if [rFromExp,rByExp,rToExp]::list(Static) then #unroll loop
#        unroller := StaticLoopUnroller(loopVar, statseq, whileExp);
#        for i from SVal(rFromExp) by SVal(rByExp) to SVal(rToExp) do
#            if not unroller:-unrollOnce(i) then break end if;
#        end do;
#        unroller:-result();
#    else
#        # need to do this because unassigned locals are considered static
#        getEnv(loopVar):-setValDynamic(Name(loopVar));
#        assigns := op(map(analyzeDynamicLoopBody, [statseq, whileExp]));
#        stmt := MWhileForFrom(loopVar, rFromExp, rByExp, rToExp, whileExp, peM(statseq));
#        `if`(nops([assigns]) > 0, MStatSeq(assigns, stmt), stmt);
#    end if;
#end proc;



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
        local res, flattened, assign, expr, env;
        res := Unfold:-UnfoldIntoAssign(residualProcedure, redCall, fullCall, gen, var);
        flattened := M:-RemoveUselessStandaloneExprs(res);
        #if nops(flattened) = 1 and op([1,0], flattened) = MSingleAssign then
        env := callStack:-topEnv();
        # TODO, rewrite this piece
        if nops(flattened) = 1 and member(op([1,0], flattened), {MAssign, MAssignToFunction}) then
            assign := op(flattened);
            expr := op(2, assign);
            if expr::Static then
                env:-put(Name(var), SVal(expr));
                return NULL;
            elif expr::Both then
                env:-put(Name(var), SVal(StaticPart(expr)));
            end if;
        elif nops(flattened) >= 1 and op([-1,0], flattened) = MAssign then
            assign := op(-1, flattened);
            expr := op(2, assign);
            if expr::Dynamic and gopts:-getPropagateDynamic() then
                env:-put(Name(var), expr);
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
        callStack:-topEnv():-put(Name(var), SVal(s));
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


# Removes locals from a dynamic expression and replaces them with new
# generated parameter names.
# Used to propagate dynamic expressions into the new environment of a function.
replaceLocalsWithNewParams := proc(replacements, expr::Dynamic) local loc;
    loc := f -> proc(n) local newParam;
        if assigned(replacements[f(n)]) then
            MParam(replacements[f(n)]);
        else
            newParam := gen(n);
            replacements[f(n)] := MParam(newParam);
            MParam(newParam);
        end if;
    end proc;
    eval(expr, [MLocal=loc(MLocal), MParam=loc(MParam)]);
end proc;


# returns an environment where static parameters are mapped to their static values
# as well as the static calls that will be residualized if the function is not unfolded
peArgList := proc(paramSeq::mform(ParamSeq), keywords::mform(Keywords), argExpSeq::mform(ExpSeq))
    local env, fullCall, redCall, numParams, equationArgs, toRemove, i, t, f,
          reduced, staticPart, val, toEnqueue, paramName, paramVal, paramSpec, reducedArgs, eqn,
          reducedArg, arg, tmp, shouldResidualize, matchedEquations,
          locals, params, toExpSeq, loc, newParams;

    env := OnENV(); # new env for function call
    env:-setLink(callStack:-topEnv());

   	fullCall := SimpleQueue(); # residual function call including statics
   	redCall  := SimpleQueue(); # residual function call without statics
   	numParams := nops(paramSeq);
   	#possibleExpSeqSeen := false;
   	# table that remembers if an argument expression was a MEquation
   	equationArgs := {}; # set(integer)
   	toRemove := {}; # set of parameter names to be removed from the parameter sequence
    i := 1; # value of i will not be used if possibleExpSeqSeen is true

    newParams := table([]); # maps replaced locals in dynamic expressions

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

   	        for val in map(() -> [args], staticPart) do
   	            toEnqueue := `if`(reduced::Both, DynamicPart(reduced), embed(op(val)));
   	            fullCall:-enqueue(toEnqueue);
   	            if reduced::Both then
   	                redCall:-enqueue(toEnqueue);
   	            end if;
                # remember if this arg was coded directly as an equation
                equationArgs := equationArgs union `if`(Header(arg)=MEquation, {i}, {});
                if i <= numParams then
                    paramSpec := op(i, paramSeq);
                    if not checkParameterTypeAssertion(val, paramSpec) then
                        val := [getParameterDefault(paramSpec)];
                    end if;
                    env:-put(Name(paramSpec), op(val));#`if`(type(val,last_name_eval),eval(val),val));
       	                toRemove := toRemove union `if`(reduced::Both, {}, {Name(paramSpec)});
                end if;
                env:-putArgsVal(i, op(val));
                i := i + 1;
       	    end do;

   	    else # dynamic
   	        fullCall:-enqueue(reduced);
            redCall:-enqueue(reduced);
            equationArgs := equationArgs union `if`(Header(arg)=MEquation, {i}, {});

            if gopts:-getPropagateDynamic() then
                env:-put(Name(op(i, paramSeq)), replaceLocalsWithNewParams(newParams, reduced));
            end if;

            i := i + 1;
   	    end if;
   	end do;

   	matchedEquations := {};
    # match up keyword arguments
    #if not possibleExpSeqSeen then
    env:-setNargs(i-1);
    # loop over arguments which are unmatched
    reducedArgs := fullCall:-toList();
    for i from numParams+1 to fullCall:-length() do # loop over arguments that haven't been matched
        if not member(i, equationArgs) then next end if; # skip if its not an equation
        reducedArg := reducedArgs[i]; # get the reduced form of the argument
        if reducedArg::Static then
            eqn := SVal(reducedArg);
            paramName := convert(lhs(eqn), string);
            matchedEquations := matchedEquations union {paramName};
            paramVal  := rhs(eqn);
            paramSpec := op(select(k -> Name(k) = paramName, keywords)); # find the matching paramspec
            if paramSpec <> NULL then
                t := TypeAssertion(paramSpec);
                if nops(t) > 0 and not type(paramVal, op(t)) then
                    #TODO, perhaps embed an error in the code?
                    error "invalid input: option `%1` expected to be of type %2, but received %3",
                    paramName, op(t), paramVal;
                end if;
                env:-put(paramName, paramVal);
                toRemove := toRemove union {paramName};
            end if;
        else
            matchedEquations := matchedEquations union {Name(op(1,reducedArg))};
            fullCall:-enqueue(reducedArg);
            redCall:-enqueue(reducedArg);
        end if;
    end do;

    # TODO, refactor this ugly code
    for paramSpec in keywords do
        if not member(Name(paramSpec), matchedEquations) then
            tmp := SVal(ReduceExp(op(Default(paramSpec))));
            env:-put(Name(paramSpec), tmp);
        end if;
    end do;

    locals := SimpleQueue();
    params := SimpleQueue();
    for loc in keys(newParams) do
        locals:-enqueue(loc);
        params:-enqueue(newParams[loc]);
    end do;

    toExpSeq := proc(q) # inserts the needed locals into the beginning of the call
        MExpSeq(qtoseq(locals), qtoseq(q));
    end proc;

    # return results as a record just so its more organized
    Record('newEnv'=env, # environment mapping parameter names to static values
           'reducedCall'=toExpSeq(redCall),  # the reduced call to be residualized if the proc is not unfolded
           'allCall'=toExpSeq(fullCall), # the call but with static arguments still in their place
           'addParams'=[qtoseq(params)],
           'removeParams'=toRemove); # parameters to remove from the parameter sequence
end proc;


# takes continuations to be applied if f results in a procedure
peFunction := proc(funRef,#::Dynamic,
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

    elif type(sfun, `procedure`) and hasOption('builtin', sfun) then
        residualize(fun, MExpSeq(ReduceExp(argExpSeq)));
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
    if not gopts:-getShareFunctions() # turns function sharing off, signatures are still stored but never used
    or not assigned(share[signature]) then
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

    if not rec:-mustResid and isUnfoldable(newProc) then
        unfold(newProc, argListInfo:-reducedCall, argListInfo:-allCall);
    else
        specializedProcs[newName] := newProc;
        call := `if`(M:-UsesArgsOrNargs(newProc), argListInfo:-allCall, argListInfo:-reducedCall);
        residualize(MString(newName), call)
    end if;
end proc;


isUnfoldable := proc(p) local unfold, hasReturn;
    #return false;
    # a funciton cannot be unfolded if there is a return inside a loop
    unfold := true;
    hasReturn := proc()
        if hasfun([args], MReturn) then
            unfold := false;
        end if;
    end proc;
    eval(p, [MWhile=hasReturn, MWhileForFrom=hasReturn, MWhileForIn=hasReturn]);
    return unfold;
end proc;


# takes inert specializedProcs and assumes static variables are on top of callStack
# called before unfold
peFunction_GenerateNewSpecializedProc := proc(m::mform(Proc), n::string, argListInfo) :: mform(Proc);
    local env, lexMap, loc, varName, body, newProc, p, newParams, newKeywords, toParamSpec;
    # attach lexical environment
    env := callStack:-topEnv();
    if not env:-hasLex() then
        lexMap := M:-CreateLexNameMap(LexSeq(m), curry(op,2));
        env:-attachLex(lexMap);
    end if;

    # create static locals
    for loc in Locals(m) do
        varName := Var(loc);
        env:-put(varName, convert(varName, '`local`'));
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
        toParamSpec := n -> MParamSpec(op(n), MType(), MDefault());
        newParams   := MParamSeq(op(map(toParamSpec, argListInfo:-addParams)), op(remove(p, Params(m))));
        newKeywords := remove(p, Keywords(m));
        newProc := subsop(1=newParams, 11=newKeywords, newProc);
    end if;

    #specializedProcs[n] := newProc;
    newProc;
end proc;


########################################################################################



end use
end module:
