SmartOps := module()
    local
        functionHandler, # table of special dynamic handlers for functions
        syntaxHandler;
    export
        HasFunctionHandler, InvokeFunctionHandler,
        HasSyntaxHandler, InvokeSyntaxHandler;

    HasFunctionHandler := n -> assigned(functionHandler[n]);
    HasSyntaxHandler   := n -> assigned(syntaxHandler[n]);

    InvokeFunctionHandler := proc(n::string, expseq::mform(ExpSeq)) local res;
        ASSERT( assigned(functionHandler[n]) );
        res := functionHandler[n](expseq);
        `if`(res = NULL, MFunction(MName(n), expseq), res);
    end proc;

    InvokeSyntaxHandler := proc(f) local res;
        ASSERT( assigned(syntaxHandler[Header(f)]) );
        res := syntaxHandler[Header(f)](op(f));
        `if`(res = NULL, f, res);
    end proc;
    
    
    
    functionHandler["nops"] := proc(expseq) local res, dyn;
        dyn := substop(op(expseq));
        if Header(dyn) = MList then
            nops(op(dyn))
        end if;
    end proc;

    functionHandler["op"] := proc(expseq) local num, data, res;
        num := op(1, expseq);
        if num::MStatic('integer') then
            num := op(num);
            data := substop(op(2, expseq));
            if Header(data) = MList and num <= nops(op(data)) then
                res := op(num, op(data));
                `if`(res::Static, op(res), res);
            end if;
        end if;
    end proc;
    
    syntaxHandler[MTableref] := proc(t, expseq) local es, i;
        if  typematch(t, MSubst(anything, MList('es'::mform(ExpSeq))))
        and typematch(expseq, MStatic('i'::integer))
        and i <= nops(es) then 
            op(i, es)
        end if;
    end proc;



end module:
