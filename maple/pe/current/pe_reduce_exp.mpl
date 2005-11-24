
# Simple expression evaluator
# reduces to a value when the expression is completely static
# reduces to residual code when the expression is dynamic

ReduceExp := module()

    description "online expression reducer for use with online partial evaluator";
    export ModuleApply;
    local env, red, reduce, unred, unreduce;



    ModuleApply := proc(exp, reductionEnv := callStack:-topEnv()) local residual;
        #print("reducing", exp);
        env := reductionEnv;
        residual := reduce(exp);
        #print("reduced", residual);
        env := 'env';
        # TODO: get rid of this extra eval
        eval(residual, [ _Tag_STATICTABLE = ((x,v) -> x),
                         _Tag_STATICEXPSEQ = (() -> args),
                         SArgs = (() -> MArgs())]);
    end proc;


    reduce := proc(exp)
        h := op(0,exp);
        if assigned(red[h]) then
            return red[h](op(exp));
        end if;
        error "reduction of %1 not supported yet", h
    end proc;


    reduceAll := proc()
        op(map(reduce, [args]))
    end proc;

    binOp := (f, op) -> proc(x, y)
        rx := reduce(x);
        ry := reduce(y);
        `if`(rx::Static and ry::Static, op(rx,ry), f(rx,ry));
    end proc;

    unOp := (f, op) -> proc(x)
        rx := reduce(x);
        `if`(rx::Dynamic, f(rx), op(rx))
    end proc;

    naryOp := (f, op) -> () -> foldl(binOp(f,op), args[1], args[2..nargs]);




    red['Integer'] := () -> args;
    red['string']  := () -> args;

    red[MSum]  := naryOp(MSum, `+`);
    red[MProd] := naryOp(MProd, `*`);

    red[MRational] := binOp(MRational, `/`);
    red[MPower]    := binOp(MPower,    `^`);
    red[MCatenate] := binOp(MCatenate, `||`);
    red[MEquation] := binOp(MEquation, `=`);
    red[MLesseq]   := binOp(MLesseq,   `<=`);
    red[MLessThan] := binOp(MLessThan, `<`);
    red[MImplies]  := binOp(MImplies,  `implies`);
    red[MAnd]      := binOp(MAnd,      `and`);
    red[MOr]       := binOp(MOr,       `or`);
    red[MXor]      := binOp(MXor,      `xor`);
    red[MRange]    := binOp(MRange,    `..`);

    red[MNot] := unOp(MNot, `not`);

    red[MInt]    := () -> args;
    red[MString] := () -> args;
    red[MFloat]  := (x,y) -> FromInert(_Inert_FLOAT(M:-FromM(x),M:-FromM(y)));


    red[MComplex]  := () -> `if`(nargs=1, args * I, args[1] + args[2] * I);
    red[MNargs]    := () -> `if`(env:-hasNargs(), env:-getNargs(), MNargs());
    red[MArgs]     := () -> SArgs(env:-getArgs());

    #red[MName]         := n -> convert(n, name);
    #red[MAssignedName] := red[MName];

    red[MName]         := reduceName(MName);
    red[MAssignedName] := reduceName(MAssignedName);


    reduceName := f -> proc(n)
        if env:-hasGlobal(f(args)) then
            globalEnv := callStack:-globalEnv();
            if globalEnv:-isStatic(n) then
                return globalEnv:-getVal(n);
            end if;
        end if;
        cn := convert(n, name);
        e := eval(cn);
        `if`(e::`procedure` or e::`module`, cn, e);
    end proc;


    red[MExpSeq] := proc()
        rs := reduceAll(args);
        `if`([rs]::list(Static), _Tag_STATICEXPSEQ(rs), MExpSeq(rs))
    end proc;

    red[MList] := proc(eseq)
        r := reduce(eseq);
        `if`(r::Static, [op(r)], MList(r))
    end proc;

    red[MSet] := proc(eseq)
        r := reduce(eseq);
        `if`(r::Static, {op(r)}, MSet(r));
    end proc;

    red[MMember] := proc(x1, x2)
        rx1 := reduce(x1);
        rx2 := reduce(x2); # TODO, this is strange semantics, the right side of a member is not evaluated like this
                           # should be able to put an eval around the body of MName
        if type(rx1, `package`) then
            SPackageLocal(rx1, rx1[rx2]);
        elif op(0,rx1) = SPackageLocal and type(op(2,rx1), `package`) then
            SPackageLocal(rx1, op(2,rx1)[rx2]);
        else
            MMember(rx1, rx2);
        end if;
    end proc;;

    red[MFunction] := proc(f, expseq)
        if f = MAssignedName("print", "PROC", MAttribute(MName("protected", MAttribute(MName("protected"))))) then
            return MFunction(f, reduce(expseq));
        end if;

        rf := reduce(f);
        re := reduce(expseq);
        if type(rf, procedure) and Header(re) = _Tag_STATICEXPSEQ then
            rf(op(re));
        elif type(rf, name) and Header(re) = _Tag_STATICEXPSEQ then
            apply(convert(op(1,rf), name), op(re));
        else
            MFunction(rf, re);
        end if;
    end proc;


    # evaluates table references as expressions
    red[MTableref] := proc(tbl, eseq) # know that both args are static
        rt := reduce(tbl);
        re := reduce(eseq);
        h := op(0, rt);
        if member(h, {_Tag_STATICTABLE, SPackageLocal}) then
	        actualTable := op(2, rt);
	        ref := op(re);
	        if assigned(actualTable[ref]) then
	            actualTable[ref];
	        else
	            MTableref(rt, re);
	        end if;
        elif h = SArgs then
            argsTbl := op(1, rt);
            ref := op(re);
            if assigned(argsTbl[ref]) then
                argsTbl[ref];
            else
                MTableref(MArgs(), re);
            end if;
        elif rt::symbol and re::Static then
            rt[re];
        else
            MTableref(rt, re);
        end if;
    end proc;

    red[MParam]     := reduceVar(MParam);
    red[MLocal]     := reduceVar(MLocal);
    red[MSingleUse] := reduceVar(MSingleUse);

    red[MLexicalLocal] := reduceLex(MLexicalLocal);
    red[MLexicalParam] := reduceLex(MLexicalParam);

    reduceVar := f -> proc(x)
        if env:-isStatic(x) then
            val := env:-getVal(x);
            if type(val, table) then
                _Tag_STATICTABLE(f(x), val);
            else
                val;
            end if;
        else
            f(x);
        end if;
    end proc;

    reduceLex := f -> proc(x)
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

    # TODO, maybe needs to call back into the
    # partial evaluator to reduce the body of the closure
    red[MProc] := proc()
        Closure(env, MProc(args));
    end proc;


    red[MUneval] := proc(e)
        if op(0,e) = MName then
            convert(op(1,e), name);
        else
            MUneval(e);
        end if;
    end proc;


end module;
