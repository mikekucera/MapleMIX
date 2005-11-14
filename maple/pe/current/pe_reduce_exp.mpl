
# Simple expression evaluator
# reduces to a value when the expression is completely static
# reduces to residual code when the expression is dynamic

ReduceExp := module()

    description "online expression reducer for use with online partial evaluator";
    export ModuleApply, isDynamic, isStatic, allStatic;
    local complex, expseq, pureFunc, makeExpseqDynamic,
          naryOp, binOp, unOp, subsList, evalName;

    subsList := [
        MSum      = naryOp(MSum,  `+`),
        MProd     = naryOp(MProd, `*`),

        MPower    = binOp(MPower,    `^`),
        MCatenate = binOp(MCatenate, `||`),
        MEquation = binOp(MEquation, `=`),
        MLesseq   = binOp(MLesseq,   `<=`),
        MLessThan = binOp(MLessThan, `<`),
        MImplies  = binOp(MImplies,  `implies`),
        MAnd      = binOp(MAnd, `and`),
        MOr       = binOp(MOr,  `or`),
        MXor      = binOp(MXor, `xor`),

        MNot      = unOp(MNot, `not`),

        MInt      = (x -> x),
        MFloat    = ((x,y) -> FromInert(_Inert_FLOAT(ToInert(x),ToInert(y)))),
        MString   = (x -> x),

        MAssignedName = massignedname,
        MName         = mname,

        MRational = `/`,
        MComplex  = complex,
        MExpSeq   = expseq,
        MList     = literalList,
        MSet      = literalSet,
        MMember   = mmember
    ];


    isStatic := x -> evalb( not M:-IsM(x) or member(op(0, x), {_Tag_STATICEXPSEQ, _Tag_STATICTABLE}) );
    isDynamic := `not` @ isStatic;
    allStatic := curry(andmap, isStatic);


    binOp := proc(f, op)
        proc(x, y) local inx, iny;
            inx, iny := isDynamic(x), isDynamic(y);

            if inx and iny then
                f(x,y)
            elif inx then
                f(x, M:-ToM(ToInert(y)));
            elif iny then
                f(M:-ToM(ToInert(x)), y);
            else
                op(x,y);
            end if;
        end proc;
    end proc;

    unOp   := (f, op) -> x -> `if`(isDynamic(x), f(x), op(x));
    naryOp := (f, op) -> () -> foldl(binOp(f,op), args[1], args[2..nargs]);


    complex := proc()
        if nargs = 1 then
            args[1] * I;
        else
            args[1] + args[2] * I;
        end if;
    end proc;

    literalList := eseq -> `if`(isStatic(eseq), [op(eseq)], MList(eseq));
    literalSet  := eseq -> `if`(isStatic(eseq), {op(eseq)}, MSet(eseq));



    # You can't pass a raw expression sequence into another function
    # because each element of the sequence becomes a separate procedure parameter.
    # For example, 5 + (1,2,3) reduces to 11 because the expression reducer
    # treats it like `+`(5,(1,2,3)) which is the same as `+`(5,1,2,3)
    # Conservative temporary solution: treat all expression sequences that occur
    # as sub-expressions as dynamic.
    expseq := proc()
        if allStatic([args]) then
            _Tag_STATICEXPSEQ(args);
        else
            makeExpseqDynamic(args);
        end if;
    end proc;



    # it will receive a reduced expression sequence
    pureFunc := proc(env)
        proc(f, expseq)
            # special case for call to typechecking function
            #if getHeader(n) = MASSIGNEDNAME and getVal(n) = "type" and nops(expseq) = 2 then
            #
            #    arg1 := op(1, expseq);
            #   typeExpr := FromInert(op(2, expseq));
            # # returns a closure that generates unique names (as strings)
            #    if isStatic(arg1) then                # if the variable already reduced to a static value
            #        return type(arg1, typeExpr);
            #    elif isInertVariable(arg1) and env:-hasTypeInfo?(getVal(arg1)) then
            #        types := env:-getTypes(getVal(arg1));
            #        try
            #            if andmap(subtype, types, typeExpr) then
            #                return true;
            #            elif andmap(`not` @ curry(subtype,typeExpr), types) then
            #                return false;
            #            end if;
            #        catch "mapped procedure":  # subtype might return FAIL, in which case generate residual code
            #            print("subtype failed", lastexception);
            #        end try;
            #    end if;


            if type(f, procedure) and Header(expseq) = _Tag_STATICEXPSEQ then
                f(op(expseq));
            elif type(f, name) and Header(expseq) = _Tag_STATICEXPSEQ then
                apply(convert(op(1,f), name), op(expseq));
            else
                MFunction(f, expseq);
            end if;

        end proc;
    end proc;


    # evaluates table references as expressions
    tableref := env -> proc(tbl, eseq) # know that both args are static
        if op(0, tbl) = _Tag_STATICTABLE then
	        actualTable := op(2, tbl);
	        ref := op(eseq);
	        if assigned(actualTable[ref]) then
	            actualTable[ref];
	        else
	           MTableref(tbl, eseq);
	        end if;
        elif op(0, tbl) = SArgs then
            argsTbl := op(1, tbl);
            ref := op(eseq);

            if assigned(argsTbl[ref]) then
                argsTbl[ref];
            else
                MTableref(MArgs(), eseq);
            end if;
        else
            error "unknown table reference"
        end if;
    end proc;


    mmember := proc(x1, x2)
        if type(x1, `package`) then
            SPackageLocal(x1, x1[x2]);
        elif op(0,x1) = SPackageLocal and type(op(2,x1), `package`) then
            SPackageLocal(x1, op(2,x1)[x2]);
        elif M:-IsM(x1) then
            MMember(x1, M:-ToM(ToInert(eval(x2))));
        else
            MMember(M:-ToM(ToInert(eval(x1))), M:-ToM(ToInert(eval(x2))));
        end if;
    end proc;


    margs  := env -> () -> SArgs(env:-getArgs());
    mnargs := env -> () -> `if`(env:-hasNargs(), env:-getNargs(), MNargs());

    massignedname := n -> convert(n, name);
    mname := n -> convert(n, name);


    # evaluates static variables
    evalName := proc(env, f)
        if type(env, `onenv`) then
            proc(x)
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
        elif type(env, table) then  # must be lexical table
            proc(x)
                FromInert(M:-FromM(env[x]));
            end proc;
        else
            proc() error "no lexical environment available" end proc;
        end if
    end proc;


    evalLex := proc(env, f)
        evalName(env:-getLex(), f);
    end proc;


    # exported expression reducing function
    ModuleApply := proc(exp, env := OnENV()) local residual;

        # TODO, reduction of a proc should be different
        if Header(exp) = MProc then
            return Closure(env, exp);
        end if;

        residual := eval(exp, [op(subsList),
                               MParam = evalName(env, MParam),
                               MLocal = evalName(env, MLocal),
                               MSingleUse = evalName(env, MSingleUse),
                               MTableref = binOp(MTableref, tableref(env)),
                               MLexicalLocal = evalLex(env, MLexicalLocal),
                               MLexicalParam = evalLex(env, MLexicalParam),
                               MFunction = pureFunc(env),
                               MArgs     = margs(env),
                               MNargs    = mnargs(env)
                              ]);

        eval(residual, [_Tag_STATICEXPSEQ = (() -> args),
                        _Tag_STATICTABLE = ((x,v) -> x),
                        SArgs = (() -> MArgs())]);
    end proc;

end module;
