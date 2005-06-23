
# Simple expression evaluator
# reduces to a value when the expression is completely static
# reduces to residual inert code when the expression is dynamic

ExprEval := module()
    export reduce_expr;
    local nary_op, bin_op, un_op, isInert;

    # there must be a better way of testing this
    isInert := proc(x)
        try
            StringTools:-RegMatch("^_Inert_", op(0, x));
        catch:
            false;
        end try;
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
        proc(x)
            if isInert(x) then
                f(x);
            else
                op(x);
            end if;
        end proc;
    end proc;
    
    
    nary_op := proc(f, op)
        () -> foldl(bin_op(f,op), args[1], args[2..nargs])
    end proc;
    

    reduce_expr := proc(exp, env::bte)
        local eval_name;

        eval_name := proc(f)
            proc(x);
                if env:-has?(x) then
                    env:-get(x);
                else
                    f(x);
                end if;
            end proc;
        end proc;
        

        eval(exp, [
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
            
            _Inert_NAME      = eval_name(_Inert_NAME),            
            
            _Inert_INTPOS    = (x -> x), 
            _Inert_INTNEG    = (x -> -x),
            _Inert_FLOAT     = ((x,y) -> FromInert(_Inert_FLOAT(ToInert(x),ToInert(y)))),
            _Inert_STRING    = (x -> x)
        ]);
           

    end proc;
    
end module;

