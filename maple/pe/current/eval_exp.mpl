
# Simple expression evaluator
# reduces to a value when the expression is completely static
# reduces to residual inert code when the expression is dynamic

EvalExp := module()
    description "online expression reducer for use with online partial evaluator";
    export reduce, isDynamic,isStatic, allStatic;
    local complex, expseq, pureFunc, makeExpseqDynamic,
          naryOp, binOp, unOp, subsList, evalName;


    subsList := [
        _Inert_SUM       = naryOp(_Inert_SUM,  `+`),
        _Inert_PROD      = naryOp(_Inert_PROD, `*`),
          
        _Inert_POWER     = binOp(_Inert_POWER,    `^`),
        _Inert_CATENATE  = binOp(_Inert_CATENATE, `||`),
        _Inert_EQUATION  = binOp(_Inert_EQUATION, `=`),
        _Inert_LESSEQ    = binOp(_Inert_LESSEQ,   `<=`),
        _Inert_LESSTHAN  = binOp(_Inert_LESSTHAN, `<`),
        _Inert_IMPLIES   = binOp(_Inert_IMPLIES,  `implies`),
        _Inert_AND       = binOp(_Inert_AND, `and`),
        _Inert_OR        = binOp(_Inert_OR,  `or`),
        _Inert_XOR       = binOp(_Inert_XOR, `xor`),
                  
        _Inert_NOT       = unOp(_Inert_NOT, `not`),           
            
        _Inert_INTPOS    = (x -> x), 
        _Inert_INTNEG    = (x -> -x),
        _Inert_FLOAT     = ((x,y) -> FromInert(_Inert_FLOAT(ToInert(x),ToInert(y)))),
        _Inert_STRING    = (x -> x),
        
        _Inert_COMPLEX   = complex,
        _Inert_EXPSEQ    = expseq,
        _Inert_LIST      = literalList,
        _Inert_SET       = literalSet
    ];


    isStatic := x -> evalb( not isInert(x) or getHeader(x) = _Tag_STATICEXPSEQ );
    isDynamic := `not` @ isStatic;
    allStatic := curry(andmap, isStatic); 


    #isDynamic := proc(x) option inline;
    #    #evalb(isInert(x) or getHeader(x) = _Tag_STATICEXPSEQ);
    #    evalb(isInert(x));
    #end proc;    
    #isStatic := `not` @ isDynamic;
    #allStatic := xs -> andmap(isStatic, xs);

    
    binOp := proc(f, op)        
        proc(x, y) local inx, iny;
            inx, iny := isDynamic(x), isDynamic(y);

            if inx and iny then
                f(x,y)
            elif inx then
                f(x, ToInert(y));
            elif iny then
                f(ToInert(x), y);
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


    literalList := eseq -> `if`(isStatic(eseq), [op(eseq)], _Inert_LIST(eseq));
    literalSet  := eseq -> `if`(isStatic(eseq), {op(eseq)}, _Inert_SET(eseq));


    tableref := proc(n, eseq)

    end proc;

    
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
    
    
    makeExpseqDynamic := proc()
        _Inert_EXPSEQ(op(map(x -> `if`(isDynamic(x), x, ToInert(x)), [args]))); 
    end proc;


    # it will receive a reduced expression sequence
    pureFunc := proc(env)
        proc(n, expseq)
            # special case for call to typechecking function
            if getHeader(n) = _Inert_ASSIGNEDNAME and getVal(n) = "type" and nops(expseq) = 2 then

                arg1 := op(1, expseq);
                typeExpr := FromInert(op(2, expseq));

                if isStatic(arg1) then                # if the variable already reduced to a static value
                    return type(arg1, typeExpr);
                elif isInertVariable(arg1) and env:-hasTypeInfo?(getVal(arg1)) then
                    types := env:-getTypes(getVal(arg1));
                    try
                        if andmap(subtype, types, typeExpr) then
                            return true;
                        elif andmap(`not` @ curry(subtype,typeExpr), types) then
                            return false;
                        end if;
                    catch "mapped procedure":  # subtype might return FAIL, in which case generate residual code
                        print("subtype failed", lastexception);
                    end try;
                end if;
            
            elif getHeader(expseq) = _Tag_STATICEXPSEQ then # if all arguments are static then call the pure func
                return apply(convert(op(1,n), name), op(expseq));
            end if;

            #residualize
            # perhaps all function calls should be split out of expressions, for unfolding
            _Inert_FUNCTION(n, expseq);
        end proc;
    end proc;


    # evaluates static variables
    evalName := (env, f) -> x -> `if`(env:-fullyStatic?(x), env:-getVal(x), f(x));


    # exported expression reducing function
    reduce := proc(exp::inert, env) local residual;
        residual := eval(exp, [op(subsList), 
                               _Inert_PARAM = evalName(env, _Inert_PARAM), 
                               _Inert_LOCAL = evalName(env, _Inert_LOCAL),
                               _Inert_NAME  = evalName(env, _Inert_NAME),
                               _Inert_FUNCTION = pureFunc(env)
                              ]);

        eval(residual, [_Tag_STATICEXPSEQ = makeExpseqDynamic]);
    end proc;
    
end module;
