
# Simple expression evaluator
# reduces to a value when the expression is completely static
# reduces to residual inert code when the expression is dynamic

ExprEval := module()
    export reduce_expr, isInert, allStatic;
    local complex, expseq, pure_func, make_expseq_dynamic,
          nary_op, bin_op, un_op, subs_list;


    subs_list := [
        _Inert_SUM       = nary_op(_Inert_SUM,  `+`),
        _Inert_PROD      = nary_op(_Inert_PROD, `*`),
          
        _Inert_POWER     = bin_op(_Inert_POWER,    `^`),
        _Inert_CATENATE  = bin_op(_Inert_CATENATE, `||`),
        _Inert_EQUATION  = bin_op(_Inert_EQUATION, `=`),
        _Inert_LESSEQ    = bin_op(_Inert_LESSEQ,   `<=`),
        _Inert_LESSTHAN  = bin_op(_Inert_LESSTHAN, `<`),
        _Inert_IMPLIES   = bin_op(_Inert_IMPLIES,  `implies`),
        _Inert_AND       = bin_op(_Inert_AND, `and`),
        _Inert_OR        = bin_op(_Inert_OR,  `or`),
        _Inert_XOR       = bin_op(_Inert_XOR, `xor`),
                  
        _Inert_NOT       = un_op(_Inert_NOT, `not`),           
            
        _Inert_INTPOS    = (x -> x), 
        _Inert_INTNEG    = (x -> -x),
        _Inert_FLOAT     = ((x,y) -> FromInert(_Inert_FLOAT(ToInert(x),ToInert(y)))),
        _Inert_STRING    = (x -> x),
        
        _Inert_COMPLEX   = complex,
        _Inert_EXPSEQ    = expseq,
        _Inert_FUNCTION  = pure_func
    ];


    # this function could also be named isDynamic
    isInert := proc(x) local res;
        res := member(op(0, x), 
            {_Inert_SUM, _Inert_PROD,
             _Inert_POWER, _Inert_CATENATE, _Inert_EQUATION, _Inert_LESSEQ,
             _Inert_LESSTHAN, _Inert_IMPLIES, _Inert_AND, _Inert_OR, _Inert_XOR,
             _Inert_NOT, _Inert_INTPOS, _Inert_INTNEG, _Inert_FLOAT, _Inert_STRING,
             _Inert_NAME,_Inert_COMPLEX, _Inert_EXPSEQ, _Inert_FUNCTION,
             _Tag_STATICEXPSEQ
            });
        return res;
    end proc;


    allStatic := proc(xs)
        andmap(x -> not isInert(x), xs)
    end proc;

    
    bin_op := proc(f, op)        
        proc(x, y)
            local inx, iny;
            inx, iny := isInert(x), isInert(y);

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
    
    
    un_op := proc(f, op)
        x -> `if`(isInert(x), f(x), op(x))
    end proc;
    
    
    nary_op := proc(f, op)
        () -> foldl(bin_op(f,op), args[1], args[2..nargs])
    end proc;
    

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
            make_expseq_dynamic(args);            
        end if;
    end proc;
    
    
    make_expseq_dynamic := proc()
        _Inert_EXPSEQ(op(map(x -> `if`(isInert(x), x, ToInert(x)), [args]))); 
    end proc;


    # it will receive a reduced expression sequence
    pure_func := proc(f, expseq)
        if op(0,expseq) = _Tag_STATICEXPSEQ then
            apply(convert(op(f), name), op(expseq));
        else
            #residualize
            _Inert_FUNCTION(f, expseq);
        end if;
        
    end proc;

    reduce_expr := proc(exp, env::bte)
        local eval_name, residual;
        
        if not isInert(exp) then
            error("reduce_expr only works on Inert code");
        end if;

        eval_name := proc(f)
            x -> `if`(env:-has?(x), env:-get(x), f(x))
        end proc;
        
        residual := eval(exp, [op(subs_list), _Inert_NAME = eval_name(_Inert_NAME)]);
        
        return eval(residual, [_Tag_STATICEXPSEQ = make_expseq_dynamic]);
    end proc;

    
end module;

