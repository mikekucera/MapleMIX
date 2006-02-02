
# Simple expression evaluator
# reduces to a value when the expression is completely static
# reduces to residual code when the expression is dynamic

ReduceExp := module()
    description "online expression reducer for use with online partial evaluator";
    export ModuleApply, Reduce;
    local treatAsDynamic, env, red, specFunc, reduce, unred, unreduce, isProtectedProc;
    
    
    Reduce := proc(exp)
        genv := OnENV();
        ModuleApply(exp, OnENV());
    end proc;
    
    ModuleApply := proc(exp, reductionEnv := callStack:-topEnv())
        env := reductionEnv;
        PEDebug:-DisplayReduceStart(exp);
        
        treatAsDynamic := false;
        reduced1 := embed(reduce(exp));
        if reduced1::Dynamic then
            res := reduced1;
        else # reduced1 is static
            treatAsDynamic := true;
            reduced2 := embed(reduce(exp));
            if reduced2::Dynamic then
                res := MBoth(reduced1, reduced2);
            else
                res := reduced1;
            end if;
        end if;
        
        env := 'env';
        PEDebug:-DisplayReduceEnd(res);
        if not res::Static then
            print("reduced", res);
        end if;
        res;
    end proc;

    reduce := proc(exp)
        h := op(0,exp);
        if assigned(red[h]) then
            red[h](op(exp));
        else
            #exp;
            error "(reduce) Reduction of %1 not supported yet", h;
        end if;        
    end proc;

    reduceCat := proc(e::mform(Catenate))
        (rcurry(convert, string) @ eval @ FromInert @ M:-FromM)(e);
    end proc;


    binOp := (f, op) -> proc(x, y)
        rx := reduce(x);
        ry := reduce(y);
        if [rx]::list(Static) and [ry]::list(Static) then
            op(eval(rx),eval(ry));
        else
            f(embed(rx), embed(ry));
        end if;
    end proc;

    unOp := (f, op) -> proc(x)
        rx := reduce(x);
        `if`(rx::Dynamic, f(rx), op(rx))
    end proc;

    naryOp := (f, op) -> proc()        
        use reduceRight = proc(rx,y) 
            ry := reduce(y);
            if [rx]::list(Static) and [ry]::list(Static) then
                op(eval(rx),eval(ry));
            else
                f(embed(rx), embed(ry));
            end if;
        end proc
        in foldl(reduceRight, reduce(args[1]), args[2..nargs])
        end use
    end proc;    
 
    
    red['Integer'] := () -> args;
    red['string']  := () -> args;
    red['symbol']  := () -> args;

    red[MStatic] := () -> args;
    red[MInt]    := () -> args;
    red[MString] := () -> args;
    red[MFloat]  := (x,y) -> FromInert(_Inert_FLOAT(M:-FromM(x),M:-FromM(y)));
    
    red[MSum]  := naryOp(MSum, `+`);
    red[MProd] := naryOp(MProd, `*`);

    red[MNot] := unOp(MNot, `not`);
    
    red[MRational] := binOp(MRational, `/`);
    red[MPower]    := binOp(MPower,    `^`);
    red[MEquation] := binOp(MEquation, `=`);
    red[MLesseq]   := binOp(MLesseq,   `<=`);
    red[MLessThan] := binOp(MLessThan, `<`);
    red[MImplies]  := binOp(MImplies,  `implies`);
    red[MAnd]      := binOp(MAnd,      `and`);
    red[MOr]       := binOp(MOr,       `or`);
    red[MXor]      := binOp(MXor,      `xor`);
    red[MRange]    := binOp(MRange,    `..`);
    
    red[MComplex]  := () -> `if`(nargs=1, args * I, args[1] + args[2] * I);
    red[MNargs]    := () -> `if`(env:-hasNargs(), env:-getNargs(), MNargs());
    
    red[MBoth] := proc(s, d)
        `if`(treatAsDynamic, d, SVal(s));
    end proc;
    
    red[MArgs] := proc() 
        if env:-hasNargs() then
            q := SimpleQueue();
            argsTbl := env:-getArgs();
            for i from 1 to env:-getNargs() do
                q:-enqueue(argsTbl[i]);
            end do;
            op(q:-toList());
        else
            MArgs();
        end if;    
    end proc;
    
    
    red[MCatenate] := proc(x,y)
        r := reduce(y);
        if r::Dynamic then
            return MCatenate(x, r);
        end if;

        # some serious trickery just to get this to work
        # here ToInert is used for its real purpose, to create an expression that can't be evaluated
        h := Header(x);
        if member(h, {MName, MAssignedName, MLocal, MParam, MGeneratedName}) then
            n := _Inert_UNEVAL(ToInert(convert(op(1,x), name)));
        elif h = MString then
            n := _Inert_UNEVAL(ToInert(op(x)));
        else
            error "left side of catenate must be a name or string";
        end if;

        op(map(curry(`||`, FromInert(n)), [r]));
    end proc;

    red[MExpSeq] := proc()
        rs := op(map(reduce, [args]));
        `if`([rs]::list(Static), rs, MExpSeq(op(map(embed, [rs]))))
    end proc;

    red[MList] := proc(eseq)
        r := reduce(eseq);
        `if`([r]::list(Static), [r], MList(r))
    end proc;

    red[MSet] := proc(eseq)
        r := reduce(eseq);
        `if`([r]::list(Static), {r}, MSet(r));
    end proc;

    red[MMember] := proc(x1, x2)
        rx1 := reduce(x1);
        rx2 := reduce(x2); # TODO, this is strange semantics, the right side of a member is not evaluated like this
        `if`([rx1]::list(Static), eval(rx1)[rx2], MMember(embed(rx1), embed(rx2)))
    end proc;;

    
    isProtectedProc := proc(assignedName)
        if Header(assignedName) <> MAssignedName then
            return false;
        end if;
        n := Name(assignedName); 
        assigned(specFunc[n]) and assignedName = M:-ProtectedForm(n);  
    end proc;
    
    
    specFunc["print"] := proc(expseq)
        return MFunction(M:-ProtectedForm("print"), embed(reduce(expseq)));
    end proc;
    
    # TODO, this is not correct, because support for evaln is not there yet
    specFunc["assigned"] := proc(expseq)
        #print("assigned", expseq);
        #env :- display();
        if nops(expseq) <> 1 then
            error "assigned expects 1 argument, but received %1", nops(expseq);
        end if;
        val := op(expseq);
        if Header(val) = MAssignedName then
            return true;
        elif val::Global then
            return genv:-isAssigned(Name(val));
        elif val::Local then
            return env:-isAssigned(Name(val));
        elif Header(val) = MTableref then
            rindex := reduce(IndexExp(val));
            var := Var(val);
            if [rindex]::list(Static) then
                if var::Global then
                    return genv:-isTblValAssigned(Name(var), rindex);
                elif var::Local then
                    return env:-isTblValAssigned(Name(var), rindex);
                end if;
            end if;
        end if;
        MFunction(M:-ProtectedForm("assigned"), embed(reduce(expseq)));
    end proc;
    
    
    
    specFunc["seq"] := proc(expseq)
        m := MFunction( M:-ProtectedForm("seq"), MExpSeq(op(map(embed, [reduce(expseq)]))) );
        eval(FromInert(M:-FromM(m)));
    end proc;
    
    specFunc["if"] := proc(expseq)
        m := MFunction( M:-ProtectedForm("if"), MExpSeq(op(map(embed, [reduce(expseq)]))) );
        eval(FromInert(M:-FromM(m)));
    end proc;
    
    
    red[MFunction] := proc(f, expseq)
        if isProtectedProc(f) then
            return specFunc[Name(f)](expseq);
        end if;
        
        rf := reduce(f);
        re := reduce(expseq);
        
        if type(rf, 'procedure') and [re]::list(Static) then
            rf(re);
        elif type(rf, name) and [re]::list(Static) then
            apply(convert(op(1,rf), name), re);
        else
            MFunction(embed(rf), embed(re));
        end if;
    end proc;



    # evaluates table references as expressions
    red[MTableref] := proc(tbl, eseq) # know that both args are static
        re := reduce(eseq);
        if Header(tbl) = MArgs then
            argsTbl := env:-getArgs();
            if assigned(argsTbl[re]) then
                return argsTbl[re]
            else
                return MTableref(MArgs(), embed(re))
            end if;
        end if;
    
        # aviod evaluating the entire table if possible
        h := Header(tbl);
        if [re]::list(Static) and member(h, {MLocal, MParam, MGeneratedName, MName, MAssignedName}) then 
        
            if member(h, {MLocal, MParam, MGeneratedName}) then
                try
                    return env:-getTblVal(Name(tbl), re);
                catch "table value is dynamic" :
                    if not env:-isStatic(Name(tbl)) then
                        return MTableref(tbl, embed(re));
                    end if;
                end try;
            elif member(h, {MName, MAssignedName}) then
                try
                    return genv:-getTblVal(Name(tbl), re);
                catch "table value is dynamic" :
                    # fall through
                end try;
            end if;
        end if;

        rt := reduce(tbl);
        if [rt]::list(Static) and [re]::list(Static) then #and assigned(rt[re]) then
            val := rt[re];
            if val = OnENV:-DYN then
                error "lookup of dynamic value in table, table expressions must be names";
            else
                return val
            end if;
        end if;
        MTableref(embed(rt), embed(re));
    end proc;

    
    red[MName] := reduceName(MName);
    red[MAssignedName] := reduceName(MAssignedName);

    reduceName := f -> proc(n) local hasDyn;
        if not assigned(genv) or genv:-isDynamic(n) then
            c := convert(n, name);
            evaled := eval(c);
            if evaled::Or(`module`, 'procedure', 'table') then
                c
            else
                evaled
            end if;
        else
            val := genv:-getVal(n, 'hasDyn');
            `if`(hasDyn and treatAsDynamic, f(n), val);
        end if
    end proc;
    
    
    red[MParam]     := reduceVar(MParam);
    red[MLocal]     := reduceVar(MLocal);
    red[MSingleUse] := reduceVar(MSingleUse);
    red[MGeneratedName] := reduceVar(MGeneratedName);

    red[MLexicalLocal] := reduceLex(MLexicalLocal);
    red[MLexicalParam] := reduceLex(MLexicalParam);

    reduceVar := f -> proc(x) local hasDyn;
        if env:-isStatic(x) then
            val := env:-getVal(x, 'hasDyn');
            `if`(hasDyn and treatAsDynamic, f(x), val);
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
    
    red[MAssignedLocalName] := proc()
        FromInert(M:-FromM(MAssignedLocalName(args)));
    end proc;


    # a closure is created
    red[MProc] := proc()
        p := MProc(args);
        if ormap(curry(`=`, MName("pe_thunk")), OptionSeq(p)) then
            thunk := FromInert(M:-FromM(p));
            thunk;
        else
            lexMap := M:-CreateLexNameMap(LexSeq(p), curry(op, 2));
            newBody := eval(ProcBody(p), MLexicalLocal = curry(replaceClosureLexical, lexMap));        
            newProc := subsop(5=newBody, 8=MLexicalSeq(), p);
            FromInert(M:-FromM(newProc));
        end if;
    end proc;

    replaceClosureLexical := proc(lexMap, n)
        closureEnv := callStack:-topEnv();
        s := op(n);
        thunk := proc()
            if closureEnv:-isStatic(s) then
                # TODO, pass hasDyn to getVal?
                closureEnv:-getVal(s);
            elif assigned(lexMap[s]) then
                if closureEnv:-hasLex() then
                    lex := closureEnv:-getLex();
                    lexName := op(lexMap[s]);
                    if assigned(lex[lexName]) then
                        FromInert(M:-FromM(lex[lexName]));
                    else
                        error "invalid lexical name: %1", s;
                    end if;
                else
                    error "can't find lexical: %1", s;
                end if;
            else
                error "dynamic lexicals in closure is not supported: %1", s; 
            end if;
        end proc;
        thunk := setattribute(eval(thunk), 'pe_thunk'); # used to identify these thunks later
        MFunction(MStatic(eval(thunk)), MExpSeq());        
    end proc;
    
    
    red[MUneval] := proc(e)
        if member(Header(e), {MName, MAssignedName, MGeneratedName, MSingleUse}) then
            convert(op(1,e), name);
        else
            MUneval(embed(e));
        end if;
    end proc;


end module;
