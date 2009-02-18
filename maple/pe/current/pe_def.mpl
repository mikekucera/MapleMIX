# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.

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
    getMCode, getMCodeFromCache, embed, getEnv, updateVar,
    pe, peM, peResidualizeStatement, peIF,
    StaticLoopUnroller,
    checkParameterTypeAssertion, getParameterDefault,
    isPossibleExpSeq, peArgList, isUnfoldable,
    peFunction, peFunction_StaticFunction,
    peFunction_SpecializeThenDecideToUnfold,
    peFunction_GenerateNewSpecializedProc,
    analyzeDynamicLoopBody, transformForCallSig,
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

# calls the specializer on the given goal function
# returns a Maple module containing the residual specialized functions
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
   	# convert goal function into M form
    m := getMCode(eval(p));
    userinfo(3, PE, "Successfully got MCode for", p);
    callStack:-push();

    try
    	# Several functions may be generated in the processes, they are all stored in this table.
    	# The specialized goal function will become the ModuleApply procedure of the returned module.
        specializedProcs["ModuleApply"] := peFunction_GenerateNewSpecializedProc(m);
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
    	# Try to transform the speclialized code into an active maple module.
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

# After the initial M code is retrieved from the cache it still
# needs to be further transformed into a DAG.
# This transforms the code such that all if statement brances end 
# with a pointer to the code that would execute after the if statment.
# This makes specialization of if statements possible.
getMCode := proc(fun)
    M:-TransformIf:-TransformToDAG(getMCodeFromCache(fun));
end proc;


# Takes any value(s) and wraps them in MStatic()
# Static values must be embedded in MStatic() in M form.
embed := proc(e)
    if nargs = 0 then
        MStatic()
    elif nargs = 1 and e::Static then
        MStatic(e)
    elif nargs = 1 and e::PseudoStatic then
        e
    elif nargs = 1 and e::Dynamic then
        e
    elif nargs = 1 and e::Both then
        e
    elif [args] :: list(Static) then
        MStatic(args);
    else
        error "illegal embed: %1", [args];
    end if;
end proc;


# Gets the environment associated with the given name.
# Returns the global environment if the name is a global and the
# environment at the top of the call stack if its a local name.
getEnv := proc(var::mname)
    `if`(var::Local, callStack:-topEnv(), genv)
end proc;

############################################################################
# Partial Evaluation of statements
############################################################################

# Used to specialize a statements. 
# Calls the appropriate function based on the statement form.
peM := proc(m::mform) local h;
    if nargs = 0 then
        return NULL;
    end if;
    h := Header(m);
    userinfo(10, PE, "PE on an", h);
    if assigned(pe[h]) then
        return pe[h](op(m));
    end if;
    error "(peM) not supported: %1", h;
end proc;

# Used to build simple functions that just reduce their expression
# and always residualize.
peResidualizeStatement := (f, e) -> f(ReduceExp(e));

#pe[MStandaloneExpr] := curry(peResidualizeStatement, MStandaloneExpr);
pe[MStandaloneExpr] := proc(e)
    # double-reduction, to take care of MPseudoStatic
    MStandaloneExpr(ReduceExp(ReduceExp(e)));
end proc;


# return and error always residualize
pe[MReturn] := curry(peResidualizeStatement, MReturn);
pe[MError]  := curry(peResidualizeStatement, MError);


# Specializes a sequence of statements.
pe[MStatSeq] := proc() :: mform(StatSeq);
    local q, i, j, h, stmt, residual, statseq, size, stmtsAfterIf, below;

    statseq := M:-FlattenStatSeq(MStatSeq(args));
    size := nops(statseq);

    q := SuperQueue();

    for i from 1 to size do
        stmt := op(i, statseq);
        h := Header(stmt);

        PEDebug:-StatementStart(stmt);

        # Loop specialization functions must also be given the code
        # that comes after the loop.
        if member(h, {MWhileForFrom, MWhileForIn}) then
            below := MStatSeq(op(i+1..size, statseq));
            residual := pe[h](op(stmt), below);
            if residual <> NULL then q:-enqueue( residual ); end if;
            PEDebug:-StatementEnd();
            break;
        end if;

        # Specialize the statement.
        residual := peM(stmt);
        PEDebug:-StatementEnd(residual);

        if residual <> NULL then
            if Header(residual) = MTry and i < size then
                error "code after a try/catch is not supported";
            end if;
            q:-enqueue(residual);
            
            # don't bother specializing unreachable code
            if M:-EndsWithErrorOrReturn(residual) then
                break
            end if;
        end if;
    end do;
    
    # Sometimes specialization results in standalone expressions that have no side effects,
    # these are removed.
    M:-RemoveUselessStandaloneExprs(MStatSeq(qtoseq(q)));
end proc;


# MRef is a special M-form statement that actually represents a pointer
# to a block of code. These are inserted when the code is transformed into a DAG.
pe[MRef] := proc(ref)
    peM(ref:-code); # this means the partial evaluator removes all references
end proc;


# Its possible to embed commands to MapleMIX in the subject code.
# These commands are useful for debugging MapleMIX.
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


# This is used to propagate information from an if statement condition into the branches of the
# statement. Currently it only works with simple equations.
# For example: 
#     if x = 0 then BODY end if; 
# In this case we know that x should equal 0 inside of BODY,
# this is very useful information that leads to much better specialization.
# The value of the variable into the environment before the body is specialized.
extractBindingFromEquationConditional := proc(rcond, {neg:=false})
    extractBinding(rcond, `if`(neg, MInequat, MEquation));
end proc;

extractBinding := proc(rcond, equattype) local n, v, i;
    if typematch(rcond, equattype('n'::mname, 'v'::Static)) then
        getEnv(n):-put(Name(n), SVal(v));
    elif typematch(rcond, equattype(MTableref('n'::mname, 'i'::Static), 'v'::Static)) then
        getEnv(n):-putTblVal(Name(n), i, SVal(v));
    end if;
end proc;

# Specialization of if statements.
# If the condition is dynamic then both branches of the statement
# must be specialized. This is made possible by the fact that the code
# is transformed into a DAG. 
pe[MIfThenElse] := proc(cond, thenBranch, elseBranch)
    local rcond, env, C1, C2, S, S1, S2, prevTopLocal, prevTopGlobal,
          stopAfterC1, stopAfterC2, result, a1, a2, a3, a4, hasNestedIf;
    rcond := ReduceExp(cond);
    
    if rcond::Static then # very simple when the condition is static
        peM(`if`(SVal(rcond), thenBranch, elseBranch));
    else
        env := callStack:-topEnv();
        # Any modifications to the environment must be undone before the else
        # branch is specialized. This is done by representing the environment as a stack.
        env:-grow();
        genv:-grow();

        # If the conditional expression is an equation then we can use that.
        extractBindingFromEquationConditional(rcond, neg=false);

        # Specialize the first branch.
        C1 := peM(CodeUpToPointer(thenBranch));

        # The first branch may have changed the state of the environment, so we need to 
        # specialize the code below the if statement with respect to that environment,
        # but not if the branch ends with a return because then it would be dead code.
        stopAfterC1 := M:-EndsWithErrorOrReturn(C1);
        S := CodeBelow(thenBranch);

        if not stopAfterC1 then
            # Grow the stack and specialize the rest of the program in the current environment.
            env:-grow();
            genv:-grow();
            S1 := peM(S); # save the results
            # Discard any changes that were made to the environment
            env:-pop();
            genv:-pop();
            # At this point the environment has been restored to the state it was in after
            # specializing just the code in the first branch of the if statement.
        end if;

        # Remember the changes that the first branch made to the environment.
        prevTopLocal := env:-pop();
        prevTopGlobal := genv:-pop();
        
        # Prepare to specialize the second branch
        env:-grow();
        genv:-grow();

        # If the conditional was actually an inequation then we know the value
        # can be set in the else branch.
        extractBindingFromEquationConditional(rcond, neg=true);

        # Specialize the else branch
        C2 := peM(CodeUpToPointer(elseBranch));
        
        S := CodeBelow(elseBranch);
        stopAfterC2 := M:-EndsWithErrorOrReturn(C2); # TODO, should not be needed

        hasNestedIf := X -> hasfun(X, MIfThenElse); 
        
        if stopAfterC1 and stopAfterC2 then
            result := MIfThenElse(rcond, C1, C2);
        elif not (hasNestedIf(C1) or hasNestedIf(C2)) and 
            env:-equalsTop(prevTopLocal) and genv:-equalsTop(prevTopGlobal) then
            # If both branches made the same changes to the environment then we can share
            # the specialized code that came after the first branch.
            S1 := `if`(stopAfterC1, peM(S), S1); # But not if the first branch ends in a return.
            result := MStatSeq(MIfThenElse(rcond, C1, C2), ssop(S1));
        else
            # Otherwise the code has to be specialized again with respect to the changes
            # made by the second branch.
            S1 := `if`(stopAfterC1, MStatSeq(), S1);
            S2 := `if`(stopAfterC2, MStatSeq(), peM(S));
            result := MIfThenElse(rcond, MStatSeq(ssop(C1), ssop(S1)), MStatSeq(ssop(C2), ssop(S2)));
        end if;
        env:-pop();
        genv:-pop();
        result;
    end if
end proc;

# Partial evaluation of assignment statments.
# The general idea is to reduce the rvalue expression and if its static
# then store the value in the environment, but muntiple assignment complicates
# the logic.
pe[MAssign] := proc(n::Or(mname,specfunc(mname,MExpSeq)), expr::mform)
    local reduced, reducedName, env, v, var, vars, shouldResidualize, exprList;
    userinfo(8, PE, "MAssign:", expr);

    # Special case when the lvalue is a catenation, need to compute the
    # names that are being assigned to.
    if Header(n) = MCatenate then
        reducedName := ReduceExp(n);
        if reducedName::Dynamic then
            return MAssign(n, ReduceExp(expr)); # TODO, maybe don't use n
        else
            vars := [op(map(MName, map((x)->convert(x,string),reducedName)))]; 
        end if
    elif Header(n) = MExpSeq then # multiple assignment
        vars := [op(n)];
    else
        vars := [n];
    end if;
    
    reduced := ReduceExp(expr);

	if nops(vars) = 1 then
	    updateVar(op(vars), reduced);
	else
		#if nops(reduced) <> nops(vars) then
		#	print("MAssign", args);
		#	print("reduced", reduced, "vars", vars);
	    #	error "unmatched multiple assignment";
	    #end if;
	    if reduced::Static then # something like MStatic(1,2,3);
	    	exprList := [op(map(MStatic,reduced))];
	    	MStatSeq(op(zip(updateVar, vars, exprList)));
	    elif Header(reduced) = MExpSeq then # its dynamic but we can still match them up, I don't think this is fully sound
	    	exprList := [op(reduced)];
	        MStatSeq(op(zip(updateVar, vars, exprList)));
	    else # its dynamic
	    	for v in vars do
	    		env := getEnv(v);
	    		env:-setValDynamic(op(v));
	    	end do;
	    	MAssign(n, reduced);
	    end if;
	end if;
end proc;


# Sets a value in the environment.
# Useful to make this a separate funciton because it can be used in a zip()
# This function is also called when specilization of an MAssignToFunction
# results in a single assignment statement.
updateVar := proc(var::mform, reduced) local env, str;
	if var::Global then # very conservative
	    callStack:-setGlobalEnvUpdated(true);
	end if;
	
	env := getEnv(var);
	str := op(var);
	if reduced::Static then
	    env:-put(str, SVal(reduced));
	    NULL;
    elif reduced::PseudoStatic then
        env:-put(str, reduced);
        NULL;
    elif reduced::Dynamic then
        env:-put(str, reduced);
        MAssign(var, reduced);
    else # Both
        env:-put(str, SVal(StaticPart(reduced)));
        MAssign(var, DynamicPart(reduced));
    end if;
end proc;


# Assignment to a table cell.
pe[MAssignTableIndex] := proc(tr::mform(Tableref), expr::mform)
    local rindex, rexpr, env, var;
    userinfo(8, PE, "MAssignTableIndex: expr", expr);
    userinfo(8, PE, "MAssignTableIndex: tr", tr);
    rindex := ReduceExp(IndexExp(tr));
    rexpr  := ReduceExp(expr);
    env := getEnv(Var(tr));
    var := Name(Var(tr)); # ToM will ensure that tableref will be a name

    userinfo(10, PE, "MAssignTableIndex: rindex", rindex);
    userinfo(10, PE, "MAssignTableIndex: rexpr", rexpr);
    userinfo(10, PE, "MAssignTableIndex: var", var);

    if Var(tr)::Global then # very conservative
        callStack:-setGlobalEnvUpdated(true);
    end if;

    if [rindex,rexpr]::[Static,Static] then
        env:-putTblVal(var, rindex, SVal(rexpr));
        NULL;

    elif [rindex,rexpr]::[Static,Both] then
        env:-putTblVal(var, rindex, SVal(StaticPart(rexpr)));
        MAssignTableIndex(subsop(2=rindex, tr), rexpr);

    elif [rindex,rexpr]::[Static,Dynamic] then
        env:-setTblValDynamic(var, rindex);
        MAssignTableIndex(subsop(2=rindex, tr), rexpr);

    else
        env:-setValDynamic(var);
        MAssignTableIndex(subsop(2=rindex, tr), rexpr);
    end if;
end proc;

# Special M-form used to handle multi-dimensional tables.
# For example
#   T[1][2] := x;
# becomes
#   m1 := T[1];
#   m1[2] := x
# where the first assignment statement is an MAssignToTable.
# This is a special case where m1 should be assigned to a table
# thats already in the environment.
pe[MAssignToTable] := proc(n::mname, expr::mform(Tableref)) 
    local tblVar, rindex, env;
    userinfo(8, PE, "MAssignToTable:", expr);
    rindex := ReduceExp(IndexExp(expr));
    tblVar := Var(expr);
    env := getEnv(tblVar);

    if not env:-isTblValAssigned(Name(tblVar), rindex) then
        env:-putTblVal(Name(tblVar), rindex, table());
    end if;

    pe[MAssign](n, expr); # TODO, this would have to change if PE was run as a fixed point
end proc;

# Very conservative approach to dynamic loops.
# Will simply residualize the entire loop, but must analyze to determine
# variables that have become dynamic.
# Any variable that is written to in the loop body should be considered dynamic,
# but any static variables will have been removed from the program up to this point
# so any static variables in the body of the loop must be residualized before the loop.
analyzeDynamicLoopBody := proc(body::mform)
    local notImplemented, readVar, readLocal, readGlobal, readTableref, writeVar, writeTable, q;
   	
    q := SuperQueue(); # assignment statements that will be residualized above the loop

    notImplemented := () -> ERROR("non-intrinsic call in dynamic loop not supported");
    #readVar := proc(n::string, env)
        #if env:-isStatic(n) then
        #    error "static value in dynamic loop body is not supported yet";
        #end if;
    #end proc;
    #readLocal  := n -> readVar(n, callStack:-topEnv());
    #readGlobal := n -> readVar(n, genv);
    readTableref := proc(var) local env, val, i, inds;
    	env := getEnv(var);
        if not env:-isDynamic(Name(var)) then # the entire table must be made dynamic
            # Get all the static indicies, generate an assignment for each
            # TODO, this is a quick way of implementing this, it probably has bad performance and can be rewritten
            inds := env:-getStaticIndices(Name(var)); # inds is a set of lists
            for i in inds do
            	val := env:-getTblVal(Name(var), MStatic(op(i)));
            	q:-enqueue(MAssignTableIndex(MTableref(var,MStatic(op(i))),MStatic(val)));
            	env:-setValDynamic(Name(var));
            end do;
        end if;
        args;
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
    writeTable := proc(tblref)
    	writeVar(Var(tblref));
	end proc;    	

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


# The m-form code for a static loop is transformed on the fly here.
# This is done to allow dynamic if statements inside of static loops.
# Special "driver" statments are inserted at the bottom of the loop
# that act like gotos, these are eventually removed.
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

# Inserts drivers into the body of a loop.
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
            MStatSeq(front, MRef(Record('code'=procname(op(last):-code, driver))))
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


# Drivers act like conditional GOTOs
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


# Unlike inert form while loops are split out into their own
# case in m-form.
pe[MWhile] := proc()
    error "While loops are not supported";
end proc;

# Support for try-catch is extremely limited.
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

    q := SuperQueue();

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

# There are two types of specializable function call, a function call all on its own
# and a function call where the return value is assigned to a variable.
# Both of these cases are ultimately handled by the peFunction method but there
# are some differences, these are handled by passing three functions to the
# peFunction method.
#
# 1) unfold: 
#        Contains the logic that should be executed is to be unfolded after specialization.
#        Unfolding MStandaloneFunction is very different from unfolding MAssignToFunction. 
#        For the MAssignToFunction case any return statements inside the function must
#        be transformed into assignment statements by the unfolding transformation. 
# 2) residualize:
#        Contains the logic to residualize the function call when the function is not unfolded.
# 3) symbolic:
#        Used when the function name isn't assigned to a procedure, so the function name
#        is just a symbol and the result should be a reduced expression.


pe[MStandaloneFunction] := proc() local unfold;
    unfold := proc(residualProcedure, redCall, fullCall)
        Unfold:-UnfoldStandalone(residualProcedure, redCall, fullCall, gen);
    end proc;
    peFunction(args, unfold, () -> MStandaloneFunction(args), () -> MStandaloneExpr(args));
end proc;


# no support for assigning to a global variable,
pe[MAssignToFunction] := proc(var::mform({Local, SingleUse}), funcCall::mform(Function))
    local unfold, residualize, symbolic;
    
    # This is called if the function is to be unfolded.
    unfold := proc(residualProcedure, redCall, fullCall)
        local res, flattened, assign, expr, env;
        env := callStack:-topEnv(); 
        env:-setValDynamic(Name(var)); # make it dynamic, will go back to static if possible
        res := Unfold:-UnfoldIntoAssign(residualProcedure, redCall, fullCall, gen, var);
        
        flattened := M:-RemoveUselessStandaloneExprs(res);
        
        # If the unfolding results in a single assignment statment then we can 
        # treat it similar to an assignment statement.
        if nops(flattened) = 1 and member(op([1,0], flattened), {MAssign, MAssignToFunction}) then
            assign := op(flattened);
            expr := op(2, assign);
            return updateVar(var, expr);
        elif nops(flattened) >= 1 and op([-1,0], flattened) = MAssign then
            assign := op(-1, flattened);
            expr := op(2, assign);
			updateVar(var,expr); # just update the environment
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


transformForCallSig := proc(x) local tbl;
    if x::Dynamic then
        DYN
    elif x::Both then
        MTable(op(op(StaticPart(x))))
    elif typematch(x, MStatic(tbl::'table')) then
        MTable(op(eval(tbl)))
    else
        x
    end if;
end proc;
    
    
# Computes a record that contains a whole bunch of information before a function is specialized.
# In particular it computes an environment that contains mappins for the static parameters to the function.
# It also computes the reduced function call that will be residualized if the function isn't unfolded.
# It also computes the call signature which is used to reuse specialized procedures.
peArgList := proc(paramSeq::mform(ParamSeq), keywords::mform(Keywords), argExpSeq::mform(ExpSeq))
    local env, fullCall, redCall, numParams, equationArgs, toRemove, i, t, f,
          reduced, staticPart, val, toEnqueue, paramName, paramVal, paramSpec, reducedArgs, eqn,
          reducedArg, arg, tmp, shouldResidualize, matchedEquations,
          locals, params, toExpSeq, loc, newParams, signature;

    env := OnENV(); # new env for function call
    env:-setLink(callStack:-topEnv());
    
   	fullCall  := SuperQueue(); # residual function call including statics
   	redCall   := SuperQueue(); # residual function call without statics
   	signature := SuperQueue();
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
   	            signature:-enqueue(transformForCallSig(reduced));
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
            signature:-enqueue(transformForCallSig(reduced));
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
            signature:-enqueue(transformForCallSig(reducedArg));
        end if;
    end do;

    # TODO, refactor this ugly code
    for paramSpec in keywords do
        if not member(Name(paramSpec), matchedEquations) then
            tmp := SVal(ReduceExp(op(Default(paramSpec))));
            env:-put(Name(paramSpec), tmp);
        end if;
    end do;

    locals := SuperQueue();
    params := SuperQueue();
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
           'callSignature'=[qtoseq(signature)],
           'removeParams'=toRemove); # parameters to remove from the parameter sequence
end proc;


# This is where partial evaluation of a function really starts.
# The passed in procedures contain logic that is different for MStandaloneFunciton and MAssignToFunction.
# This function just basically filters out the case when the function name is dynamic and therefore
# the call should be residualized. 
# If the function is static and is to be specialized it is passed to peFunction_StaticFunction.
peFunction := proc(funRef,#::Dynamic,
                   argExpSeq::mform(ExpSeq),
                   unfold::procedure,
                   residualize::procedure,
                   symbolic::procedure)
    local fun, sfun, newName, ma, redargs, res, valmap, lexMap,
          newBody, newProc;
    PEDebug:-FunctionStart(funRef);
    userinfo(10, PE, "Reducing function call", funRef);

    # Start by calling the reducer on the function name (actually it could be a more complex expression too).
    fun := ReduceExp(funRef); 
    
    if typematch(fun, 'MSubst'(anything, sfun::PseudoStatic)) then
        # need to look up all the names in the environment, put
        # them in, and Reduce that.  This is done by ReduceExp!
        sfun := ReduceExp(sfun);
    elif fun::Dynamic then
        # The reducer returned a dynamic value, so we have no choice but to residualize the function call.
        res := residualize(fun, ReduceExp(argExpSeq));
        PEDebug:-FunctionEnd();
        return res;
    else
        sfun := SVal(fun);
    end if;

    if type(sfun, `procedure`) and not ormap(hasOption, ['builtin'], sfun) then
        # if the procedure is builtin then do what the else clause does
        if type(funRef, mform(Procname)) then
        	newName := gen("procname_");
        elif nops(funRef) > 0 then
        	newName := gen(cat(op(1,funRef),"_"));
        else
        	newName := gen("unknownFunction_");
        end if;
        
        # After generating a new name we need to unfold the function and do some other stuff
        peFunction_StaticFunction(funRef, sfun, sfun, argExpSeq, newName, unfold, residualize, symbolic);

    elif type(sfun, `indexed`) and type(op(0,sfun), `procedure`) then
    	newName := gen(cat(op([1,1], funRef), "_"));
        
    	peFunction_StaticFunction(funRef, op(0,sfun), sfun, argExpSeq, newName, unfold, residualize, symbolic);
    
	elif type(sfun, `module`) then
		# if we got a module then thats really a call to ModuleApply
	
	    if member(convert("ModuleApply",name), sfun) then
	        ma := sfun:-ModuleApply;
	    else
            # need the full eval, because we need to op into it
            ma := op(select(x->evalb(convert(x,string)="ModuleApply"), [op(3,eval(sfun))]));
            if ma = NULL then error "package does not contain ModuleApply" end if;
        end if;
	    peFunction_StaticFunction(funRef, ma, sfun, argExpSeq, gen("ma"), unfold, residualize, symbolic);

    elif type(sfun, `procedure`) and hasOption('builtin', sfun) then
    	# builtin functions are always residualized, includeing those specified in the options
        residualize(fun, MExpSeq(ReduceExp(argExpSeq)));
    else 
        redargs := ReduceExp(argExpSeq);
        # if the funciton name was a symbol then residualize it as an expression
        if [redargs]::list(Static) then 
            symbolic(embed( apply(sfun, SVal(redargs)) ));
        else
            # Final case, nothing else to do but residualize
            residualize(fun, MExpSeq(redargs));
        end if;
    end if;
end proc;



# At this point we have a static function and we are going to specialize it.
# This function basically checks to see if there is an option associated with
# this function. For example it is possible to pass an option that says to
# treat a function as intrisic. If there is no option then the function is
# just passed along to peFunction_SpecializeThenDecideToUnfold.
peFunction_StaticFunction := proc(funRef::Dynamic,
                                  fun::procedure,
                                  funName, # procname must be bound to the name used to invoke the procedure
                                  argExpSeq::mform(ExpSeq),
                                  newName, unfold, residualize, symbolic)
    local funOption, rcall, executeTheFunction, tmp;
    if gopts:-hasFuncOpt(fun) then
        funOption := gopts:-funcOpt(fun);
        userinfo(5, PE, "StaticFunction: About to reduce", argExpSeq);
        
        rcall := ReduceExp(ReduceExp(argExpSeq));
        userinfo(5, PE, "StaticFunction: Arguments for call is", rcall);

        # If a function is PURE or INTRINSIC and the argument sequence is static
        # then we can just call the function right here and residualize the result.
        executeTheFunction := () -> (symbolic @ embed @ fun @ SVal)(rcall);

        
        if funOption = PURE then
            `if`(rcall::Static, executeTheFunction(), peFunction_SpecializeThenDecideToUnfold(args[2..-1]))
        elif funOption = INTRINSIC then 
             # intrinsic functions are always residualized
            `if`(rcall::Static, executeTheFunction(), residualize(funRef, rcall))
        elif funOption = DYNAMIC then
            residualize(funRef, rcall)
        else
            error "unknown function option %1", funOption;
        end if;
    else
        peFunction_SpecializeThenDecideToUnfold(args[2..-1]);
    end if;
end proc;


# Prepares for specializing the function by:
#  - computing an new environment for the function and pushing it on the call stack
#  - computes the call signature
#  - generates a name for the new function
# Then after the function is specialized it decides weather to unfold it or not.  
peFunction_SpecializeThenDecideToUnfold :=
    proc(fun::procedure, funName, argExpSeq::mform(ExpSeq), generatedName, unfold, residualize, symbolic)
    local m, argListInfo, newProc, newName, rec, signature, call;

	m := getMCode(eval(fun));
    newName := generatedName;

    argListInfo := peArgList(Params(m), Keywords(m), argExpSeq);
    signature := fun, eval(argListInfo:-callSignature,1);

    # handle sharing issues
    if not gopts:-getShareFunctions() # turns function sharing off, signatures are still stored but never used
    or not assigned(share[signature]) then
        rec := Record('code', 'procName', 'mustResid', 'finished');
        rec:-procName := newName;
        rec:-mustResid := false;
        rec:-finished  := false;
        share[signature] := rec;

        # bind procname
    	argListInfo:-newEnv:-put("procname", funName);
    
        callStack:-push(argListInfo:-newEnv);
        # at this point rec:-finished is false
        newProc := peFunction_GenerateNewSpecializedProc(m, argListInfo);
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
        unfold(newProc, argListInfo:-reducedCall, eval(argListInfo:-allCall,1));
    else
        specializedProcs[newName] := newProc;
        call := `if`(M:-UsesArgsOrNargs(newProc), eval(argListInfo:-allCall,1), argListInfo:-reducedCall);
        residualize(MString(newName), call)
    end if;
end proc;


isUnfoldable := proc(p) local unfold, hasReturn;
    # a function cannot be unfolded if there is a return inside a loop
    unfold := true;
    hasReturn := proc()
        if hasfun([args], MReturn) then
            unfold := false;
        end if;
    end proc;
    eval(p, [MWhile=hasReturn, MWhileForFrom=hasReturn, MWhileForIn=hasReturn]);
    return unfold;
end proc;


# This is where the body of the function is actually specialized.
# A new specialized procedure is returned.
peFunction_GenerateNewSpecializedProc := proc(m::mform(Proc), argListInfo) :: mform(Proc);
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
    if nargs > 1 and not M:-UsesArgsOrNargs(newProc) then
        # This needs to be here because SetArgsFlags is called after partial evaluation of body of proc
        #p := x -> env:-isDynamic(Name(x));
        p := x -> member(Name(x), argListInfo:-removeParams);
        toParamSpec := n -> MParamSpec(op(n), MType(), MDefault());
        newParams   := MParamSeq(op(map(toParamSpec, argListInfo:-addParams)), op(remove(p, Params(m))));
        newKeywords := remove(p, Keywords(m));
        newProc := subsop(1=newParams, 11=newKeywords, newProc);
    end if;

    newProc;
end proc;


########################################################################################



end use
end module:
