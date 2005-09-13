
# Simple expression evaluator
# reduces to a value when the expression is completely static
# reduces to residual inert code when the expression is dynamic

EvalExp := module()
    description "online expression reducer for use with online partial evaluator";
    export reduce, isDynamic, allStatic;
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
        _Inert_EXPSEQ    = expseq
        #_Inert_FUNCTION  = pureFunc
    ];


    # this function could also be named isDynamic
    isDynamic := proc(x)
        member(op(0, x), 
            {_Inert_SUM, _Inert_PROD,
             _Inert_POWER, _Inert_CATENATE, _Inert_EQUATION, _Inert_LESSEQ,
             _Inert_LESSTHAN, _Inert_IMPLIES, _Inert_AND, _Inert_OR, _Inert_XOR,
             _Inert_NOT, _Inert_INTPOS, _Inert_INTNEG, _Inert_FLOAT, _Inert_STRING,
             _Inert_NAME,_Inert_COMPLEX, _Inert_EXPSEQ, _Inert_FUNCTION,        
             _Inert_PARAM, _Inert_LOCAL,
             _Tag_STATICEXPSEQ
            });        
    end proc;


    allStatic := proc(xs)
        andmap(`not` @ isDynamic, xs)
    end proc;

    
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
            #if op(0, n) = _Inert_ASSIGNEDNAME and op(1, n) = "type" then
            #    print("call to type");
            
            if op(0,expseq) = _Tag_STATICEXPSEQ then # if all arguments are static then call the pure func
                apply(convert(op(n), name), op(expseq));
            else
                #residualize
                # perhaps all function calls should be split out of expressions, for unfolding
                _Inert_FUNCTION(n, expseq);
            end if;
        end proc;
    end proc;


    # evaluates static variables
    evalName := (env, f) -> x -> `if`(env:-fullyStatic?(x), env:-getVal(x), f(x));


    # exported expression reducing function
    reduce := proc(exp::inert, env) local residual;                
        residual := eval(exp, [op(subsList), 
                               _Inert_PARAM = evalName(env, _Inert_PARAM), 
                               _Inert_LOCAL = evalName(env, _Inert_LOCAL),
                               _Inert_FUNCTION = pureFunc(env)
                              ]);

        eval(residual, [_Tag_STATICEXPSEQ = makeExpseqDynamic]);
    end proc;
    
end module;
