# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.

# Simple expression evaluator
# reduces to a value when the expression is completely static
# reduces to residual code when the expression is dynamic

ReduceExp := module()
    description
        "online expression reducer for use with online partial evaluator";
    export
        ModuleApply, Reduce;
    local
        SmartOps,
        reduce, binOp, mcarthyOp, unOp, naryOp, red, isProtectedProc, specFunc,
        reduceName, reduceVar, reduceLex, evalBinOpAfterReduce,
        env, treatAsDynamic, reducedTable;

$include "pe_reduce_smarter.mpl"

    Reduce := proc(expr)
        genv := OnENV();
        ModuleApply(expr, OnENV());
    end proc;

    ModuleApply := proc(expr, reductionEnv := callStack:-topEnv())
        local reduced1, reduced2, res;
        env := reductionEnv;
        
        userinfo(2, PE, sprintf("reducing %a", expr));

        PEDebug:-DisplayReduceStart(expr);

        treatAsDynamic := false;
        reducedTable := false;

        reduced1 := embed(reduce(expr));

        if reducedTable and reduced1::Static then
            treatAsDynamic := true;
            reduced2 := embed(reduce(expr));
            if reduced2::Dynamic then
                res := MBoth(reduced1, reduced2);
            else
                res := reduced1;
            end if;
        else
            res := reduced1;
        end if;
        
        userinfo(2, PE, sprintf("reduced to %a",res));
        
        env := 'env';
        PEDebug:-DisplayReduceEnd(res);
        res;
    end proc;

    reduce := proc(expr) local h, res;
        h := Header(expr);
        if assigned(red[h]) then
            res := [red[h](op(expr))];
            if res::list(Dynamic) and SmartOps:-HasSyntaxHandler(h) then
                SmartOps:-InvokeSyntaxHandler(op(res));
            else
                op(res);
            end if;
        else
            error "(reduce) Reduction of %1 not supported yet", h;
        end if;
    end proc;


    binOp := (f, oper) -> proc(x, y) local rx, ry,a,b;
        rx := [reduce(x)];
        ry := [reduce(y)];
        evalBinOpAfterReduce(f, oper, rx,ry);
    end proc;
    

    # short circut semantics for boolean operators
    mcarthyOp := (f, oper, shortCircuitTest, shortCircuitResult) -> proc(x,y) local rx, ry;
    	rx := [reduce(x)];
    	if rx::list(Static) and nops(rx) = 1 and evalb(op(rx)) = shortCircuitTest then
    		shortCircuitResult;
    	else
    		ry := [reduce(y)];
    		evalBinOpAfterReduce(f, oper, rx,ry);
    	end if;
    end proc;
    
    
    evalBinOpAfterReduce := proc(f, oper, rx, ry) local a, b;
    	if rx::list(Static) and ry::list(Static) then
    		# this does not allow x or y to be an expseq...
            # oper(op(rx),op(ry));
    		subs(a=op(rx), b=op(ry), oper('a','b'));
    	else
    		f(embed(op(rx)), embed(op(ry)));
    	end if;
    end proc;

    unOp := (f, oper) -> proc(x) local rx;
        rx := [reduce(x)];
        `if`(rx::list(Dynamic), f(op(rx)), oper(op(rx)))
    end proc;


    naryOp := (f, oper) -> proc() local i, q, rt1, rt2;
        q := SimpleQueue();
        rt1 := [reduce(args[1])];
        
        for i from 2 to nargs do
            rt2 := [reduce(args[i])];
            if rt1::list(Static) and rt2::list(Static) then
                rt1 := [oper(op(rt1), op(rt2))];
            else
                q:-enqueue(embed(op(rt1)));
                if i = nargs then
                    q:-enqueue(embed(op(rt2)));
                else 
                    rt1 := rt2;
                end if;
            end if;
        end do;

        `if`(q:-empty(), op(rt1), f(qtoseq(q)));
    end proc;

    red[MRational] := binOp(MRational, `/`);
    red[MPower]    := binOp(MPower,    `^`);
    red[MEquation] := binOp(MEquation, `=`);
    red[MInequat]  := binOp(MInequat,  `<>`);
    red[MLesseq]   := binOp(MLesseq,   `<=`);
    red[MLessThan] := binOp(MLessThan, `<`);
    red[MRange]    := binOp(MRange,    `..`);
    red[MXor]      := binOp(MXor,     `xor`);
    
    red[MDColon]   := binOp(MDColon,  `::`);

    red[MNot] := unOp(MNot, `not`);

    red[MSum]  := naryOp(MSum,  `+`);
    red[MProd] := naryOp(MProd, `*`);

    red['Integer'] := () -> args;
    red['string']  := () -> args;
    red['symbol']  := () -> args;

    red[MStatic] := () -> args;
#    red[MBoth]   := (s, d) -> `if`(treatAsDynamic, d, SVal(s));
    red[MBoth]   := MBoth;

    red[MInt]    := () -> args;
    red[MString] := () -> args;
    red[MFloat]  := (x,y) -> FromInert(_Inert_FLOAT(M:-FromM(x),M:-FromM(y)));

    red[MComplex] := () -> `if`(nargs=1, args * I, args[1] + args[2] * I);
    red[MNargs]   := () -> `if`(env:-hasNargs(), env:-getNargs(), MNargs());
    red[MArgs]    := () -> `if`(env:-hasNargs(), env:-getArgs(), MArgs());

    red[MImplies]  := mcarthyOp(MImplies, `implies`, false, true  );
    red[MAnd]      := mcarthyOp(MAnd,     `and`,     false, false );
    red[MOr]       := mcarthyOp(MOr,      `or`,      true,  true  );
    
   

    red[MCatenate] := proc(x,y) local r, h, n;
        r := [reduce(y)];
        if r::list(Static) then # Dynamic then
            # some serious trickery just to get this to work
            # here ToInert is used for its real purpose, to create an expression that can't be evaluated
            h := Header(x);
            if member(h, {MName, MAssignedName, MLocal, MParam, MGeneratedName}) then
                n := _Inert_UNEVAL(ToInert(convert(Name(x), name)));
            elif h = MString then
                n := _Inert_UNEVAL(ToInert(op(x)));
            else
                error "left side of catenate must be a name or string";
            end if;

            op(map(curry(`||`, FromInert(n)), r));
        else
            MCatenate(x, op(r));
        end if;
    end proc;


    red[MExpSeq] := proc() local rs;
        rs := map(reduce, [args]);
        if rs::list(Static) then
            op(rs)
        elif type(rs, [mform(ExpSeq)]) then #Header(rs) = MExpSeq then
            op(rs)
        else
            MExpSeq(op(map(embed, rs)));
        end if;
        
        #`if`(rs::list(Static), op(rs), ))
    end proc;


    red[MList] := proc(eseq) local r;
        r := [reduce(eseq)];
        `if`(r::list(Static), r, MList(op(r)));        
    end proc;

    red[MSet] := proc(eseq) local r;
        r := {reduce(eseq)};
        `if`(r::set(Static), r, MSet(op(r)));
    end proc;

    red[MMember] := proc(x1, x2) local rx1, rx2;
        userinfo(7, PE, "MMember reducing", x1, x2);
        rx1 := [reduce(x1)];
        rx2 := reduce(x2); # TODO, this is strange semantics, the right side of a member is not evaluated like this
        `if`(rx1::list(Static), op(rx1)[rx2], MMember(embed(op(rx1)), embed(rx2)))
    end proc;;


    isProtectedProc := proc(assignedName) local n;
        if Header(assignedName) <> MAssignedName then
            return false;
        end if;
        n := Name(assignedName);
        assigned(specFunc[n]) and assignedName = M:-ProtectedForm(n);
    end proc;

    # below is support for some special functions that have their own uniqe syntax
    # TODO, print should be treated in a special way
    specFunc["print"] := proc(expseq)
        lprint("warning, a print statement was encountered");
        return MFunction(M:-ProtectedForm("print"), embed(reduce(expseq)));
    end proc;

    # TODO, this is not correct, because support for evaln is not there yet
    specFunc["assigned"] := proc(expseq) local val, rindex, var, index;
        if nops(expseq) <> 1 then
            error "assigned expects 1 argument, but received %1 arguments", nops(expseq);
        end if;

        val := op(expseq); # we know that nops(expseq) = 1

        if Header(val) = MAssignedName then
            return true;
        elif val::Global then
            return genv:-isAssigned(Name(val));
        elif val::Local then
            return env:-isAssigned(Name(val));
        elif typematch(val, MTableref('var'::mform, 'index'::mform)) then

            rindex := [reduce(index)];
            ASSERT( nops(rindex) = 1, "table index must not be an expression sequence" );

            if rindex::list(Static) then
                if var::Global then
                    return genv:-isTblValAssigned(Name(var), MStatic(op(rindex)));
                elif var::Local then
                    return env:-isTblValAssigned(Name(var), MStatic(op(rindex)));
                end if;
            end if;
        end if;
        MFunction(M:-ProtectedForm("assigned"), embed(reduce(expseq)));
    end proc;


    specFunc["seq"] := proc(expseq) local r, m, s, e, x, i, q, n, result;
        if nops(expseq) = 2 then
            r := [reduce(op(2,expseq))];
            if typematch(r, ['x'::symbol=('s'::integer)..('e'::integer)] ) then
                env:-grow();
                q := SimpleQueue();
                n := convert(x,string);
                for i from s to e do
                    env:-put(n, i);
                    r := [reduce(op(1,expseq))];
                    if nops(r) > 0 then
                        q:-enqueue(op(r));
                    end if;
                end do;
                env:-pop();
                result := q:-toList();
                if result::list(Static) then
                    return result;
                else
                    return MExpSeq(op(map(embed, result)));
                end if;                
            end if;  
        end if;

        MFunction( M:-ProtectedForm("seq"), MExpSeq(op(map(embed, [reduce(expseq)]))) )
    end proc;
    
    specFunc["if"] := proc(expseq) local c, x, y, rc, rx, ry, place;
    	if typematch(expseq, MExpSeq('c'::mform, 'x'::mform, 'y'::mform)) then
    		rc, rx, ry := [reduce(c)], [reduce(x)], [reduce(y)];
    		if rc = [true] then
    		    op(rx);
    		elif rc = [false] then
    		    op(ry);
    		else # its dynamic or its a type error, residualize in either case
    		    place := (expr) -> `if`(expr::list(Static), embed(op(expr)), op(expr));
    		    MFunction(M:-ProtectedForm("if"), MExpSeq(place(rc), place(rx), place(ry)));
    		end if;
    	else
    	    error "wrong number of arguments to `if`";
    	end if;
    end proc;

    specFunc["assign"] := proc(expseq)
        userinfo(8, PE, "reducing a call to assign");
        if nops(expseq) <> 2 then error "invalid call to assign"; end if;
        MAssign(op(map(reduce, expseq)));
    end proc;

    # TODO, what to do about this?
    # specFunc_eval := n -> proc(expseq)
    #     MFunction(M:-ProtectedForm(n), MExpSeq(op(map(embed, [reduce(expseq)]))));
    # end proc;
    # specFunc["eval"] := specFunc_eval("eval");
    # specFunc["evalb"] := specFunc_eval("evalb");
    # specFunc["evaln"] := specFunc_eval("evaln");

    red[MFunction] := proc(f, expseq) local rf, re;
        if isProtectedProc(f) then
            return specFunc[Name(f)](expseq);
        end if;

        # TODO: this is wrong, if the argument list isn't static
        # and the function name is static then we have an error
        # all static names must be removed from the residual program
        rf := [reduce(f)];
        re := [reduce(expseq)];

        if rf::list(Or('procedure','name')) then
            if re::list(Static) then
                return op(rf)(op(re))
            elif SmartOps:-HasFunctionHandler(Name(f)) then
                return SmartOps:-InvokeFunctionHandler(Name(f), op(re));
            end if;
        end if;
        MFunction(embed(op(rf)), embed(op(re)));
    end proc;



    # evaluates table references as expressions
    # know that both args are static
    red[MTableref] := proc(tbl, eseq) local re, rt, val, h;
        userinfo(7, PE, "MTableref reducing", tbl, eseq);
        re := [reduce(eseq)];
        if Header(tbl) = MArgs then
            if env:-hasArgsVal(op(re)) then
                h := [env:-getArgsVal(op(re))];
                userinfo(8, PE, "getArgsVal []", h);
                return op(h);
            else
                return MTableref(MArgs(), embed(op(re)))
            end if;
        end if;

        # aviod evaluating the entire table if possible
        if re::list(Static) and tbl::mname then
            ASSERT( not tbl::mform(Catenate), "can't use MCatenate to lookup into environment" );
            if tbl::Local then
                try
                    return env:-getTblVal(Name(tbl), MStatic(op(re)));
                catch "table value is dynamic" :
                    if env:-isStaticTable(Name(tbl)) then
                        return MTableref(tbl, embed(op(re)));
                    end if;
                end try;
            elif tbl::Global then
                try
                    return genv:-getTblVal(Name(tbl), MStatic(op(re)));
                catch "table value is dynamic" : # fall through
                end try;
            end if;
        end if;
        
        rt := [reduce(tbl)];
        if rt::list(Static) and re::list(Static) then
            val := [op(rt)[op(re)]];
            if val = [OnENV:-DYN] then
                error "lookup of dynamic value in table, table expressions must be names";
            end if;
            op(val);
        else
            MTableref(embed(op(rt)), embed(op(re)));
        end if;
    end proc;

    

    reduceName := proc(n) local hasDyn, cc, expr;
        userinfo(2, 'PE', args);
        if not assigned(genv) or not genv:-isGettable(n) then
            (c-> `if`(type(c, 'last_name_eval'), c, eval(c)))(convert(n,'name'));
        elif hasDyn and treatAsDynamic then
            __F(n);
        else
            expr := genv:-get(n, 'hasDyn');
            if expr :: Dynamic then
                MSubst(n, expr);
            else
                expr
            end if;
        end if
    end proc;

    red[MName] := subs(__F=MName, eval(reduceName));
    red[MAssignedName] := subs(__F=MAssignedName, eval(reduceName));
    
	red[MProcname] := proc()
		if not env:-isGettable("procname") then
			error("procname not set in environment");
		end if;
		env:-get("procname");
	end proc;
	
    reduceVar := proc(x) local hasDyn, expr;
        if env:-isGettable(x) then
            expr := [env:-get(x, 'hasDyn')];
            if hasDyn and treatAsDynamic then
                return __F(x);
            end if;

            if expr :: list(Static) then
                if type(op(expr), 'table') then
                    reducedTable := true;
                end if;
                op(expr);
            # in the PseudoStatic case, reduce it now
            elif expr :: list(PseudoStatic) then
                reduce(op(expr))
            else
                MSubst(__F(x), op(expr));
            end if;
        else
            __F(x);
        end if;
    end proc;

    # these evals are needed to get at the actual proc generated
    # they make debugging easier
    red[MLocal]     := subs(__F=MLocal, eval(reduceVar));
    red[MSingleUse] := subs(__F=MSingleUse, eval(reduceVar));
    red[MGeneratedName] := subs(__F=MGeneratedName, eval(reduceVar));

    red[MParam]     := subs(__F=MParam, eval(reduceVar));

    reduceLex := proc(x) local lex;
        if not env:-hasLex() then
            error "no lexical environment available";
        end if;
        lex := env:-getLex();
        if assigned(lex[x]) then
            FromInert(M:-FromM(lex[x]));
        else
            error "cannot find '%1' in lexical environment: %2", x, [op(lex)];
        end if
    end proc;

    red[MLexicalLocal] := eval(reduceLex);
    red[MLexicalParam] := eval(reduceLex);

    red[MAssignedLocalName] := () -> FromInert(M:-FromM(MAssignedLocalName(args)));
    red[MLocalName] := () -> FromInert(M:-FromM(MLocalName(args)));

    # a closure is created
    red[MProc] := proc() local p, l, newBody, newProc;
        p := MProc(args);
        l := LexSeq(p);
        if nops(l) = 0 then # completely static
            return FromInert(M:-FromM(p));
        else
            # take care of things later
            return MPseudoStatic(MProc(args));
        end if;
    end proc;


    red[MPseudoStatic] := proc(p) 
        local valmap, lexMap, newBody, newProc;
        valmap := x -> embed(reduce(op(2,x)));
        lexMap := M:-CreateLexNameMap(LexSeq(p), valmap);
        newBody := eval(ProcBody(p), MLexicalLocal=(x->lexMap[x]));
        newProc := subsop(5=newBody, 8=MLexicalSeq(), p);
        FromInert(M:-FromM(newProc));
    end proc;

    red[MUneval] := proc(e)
        if member(Header(e), {MName, MAssignedName}) then
            if type(convert(Name(e), name), protected) then
                FromInert(_Inert_UNEVAL(ToInert(convert(Name(e), name))));
            else
                `tools/gensym`(Name(e));
            end if;
        elif member(Header(e), {MGeneratedName, MSingleUse, MLocal}) then
            FromInert(_Inert_UNEVAL(ToInert(convert(Name(e), `local`))));
        else
            #error "dynamic uneval not supported";
            MUneval(embed(e));
        end if;
    end proc;

    red[MSubst] := proc(n, e)
        MSubst(n, reduce(e))
    end proc;
end module;
