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

    syntaxHandler[MProd] := proc()
        if ormap(curry(`=`, MStatic(0)), [args]) then
            0
        end if;
    end proc;

    functionHandler["nops"] := proc(expseq) local res, dyn;
        print("nops", args);
        dyn := substop(op(expseq));
        if Header(dyn) = MList and andmap(x -> member(Header(x), {MParam, MLocal, MStatic}) , op(dyn)) then
            nops(op(dyn))
        end if;
    end proc;

    functionHandler["op"] := proc(expseq) local num, data, res, es;
        num := op(1, expseq);
        if num::MStatic('integer') then
            num := op(num);
            data := substop(op(2, expseq));
            if Header(data) = MList and num <= nops(op(data)) then
                res := op(num, op(data));
                `if`(res::Static, op(res), res);
            elif Header(data) = MSum and num <= nops(data) then
                res := op(num, data);
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

    functionHandler["degree"] := proc(expseq) local s, failed, handleProd, coeffs, x;
        if typematch(expseq, MExpSeq('s'::specfunc(anything,MSum), MStatic('x'::anything)))
        or typematch(expseq, MExpSeq(MSubst(anything, 's'::specfunc(anything,MSum)), MStatic('x'::anything))) then
            failed := false;
            handleProd := proc(prod) local i;
                if typematch(prod, MProd(anything, MStatic('i'::algebraic))) then
                    degree(i, x)
                elif member(Header(prod), {MParam, MLocal}) then
                    0
                else
                    failed := true;
                end if;
            end proc;
            coeffs := map(handleProd, s);
            `if`(failed, NULL, max(op(coeffs)));
        end if;
    end proc;

    functionHandler["coeff"] := proc(expseq) local s, x, i, n, term;
        if typematch(expseq, MExpSeq(MSubst(anything, 's'::specfunc(anything,MSum)), MStatic('x'::symbol), MStatic('i'::integer))) then
            for term in s do
                if typematch(term, MProd('n'::anything, MStatic('y'::anything))) and y = x^i then
                    return n;
                elif member(Header(term), {MParam, MLocal}) and i = 0 then
                    return term;
                end if;
            end do;
        end if;
    end proc;

    syntaxHandler[MList] := proc(expseq) local doOp;

        doOp := proc(x) local es;
            if typematch(x, MFunction(MName("op"), MExpSeq(MSubst(anything, MList('es'::specfunc(anything,MExpSeq)))))) then
                op(es);
            else
                x
            end if;
        end proc;

        MList(map(doOp, expseq));
    end proc;

end module:
