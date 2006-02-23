
# Simple expression evaluator
# reduces to a value when the expression is completely static
# reduces to residual code when the expression is dynamic

ReduceExp := module()
    description 
        "online expression reducer for use with online partial evaluator";
    export 
        ModuleApply, Reduce;
    local 
        reduce, binOp, unOp, naryOp, red, isProtectedProc, specFunc,
        reduceName, reduceVar, reduceLex, replaceClosureLexical,
        env, treatAsDynamic;
    
    
    Reduce := proc(exp)
        genv := OnENV();
        ModuleApply(exp, OnENV());
    end proc;
    
    ModuleApply := proc(exp, reductionEnv := callStack:-topEnv())
        local reduced1, reduced2, res;
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
        
        #if type(res, 'MStatic(anyindex(identical(Domains:-CoefficientRing)))') then
        #    print("found tit", exp);
        #    env:-display();
        #    print("D", env:-getVal("D"));
        #end if;
        env := 'env';
        PEDebug:-DisplayReduceEnd(res);
        res;
    end proc;

    reduce := proc(exp) local h;
        h := op(0,exp);
        if assigned(red[h]) then
            red[h](op(exp));
        else
            error "(reduce) Reduction of %1 not supported yet", h;
        end if;        
    end proc;


    binOp := (f, oper) -> proc(x, y) local rx, ry;
        rx := [reduce(x)];
        ry := [reduce(y)];
        ASSERT(nops(rx)=1 and nops(ry)=1);
        if rx::list(Static) and ry::list(Static) then
            oper(op(rx),op(ry));
        else
            f(embed(op(rx)), embed(op(ry)));
        end if;
    end proc;

    unOp := (f, oper) -> proc(x) local rx;
        rx := [reduce(x)];
        `if`(rx::Dynamic, f(op(rx)), oper(op(rx)))
    end proc;

    naryOp := (f, oper) -> proc() local ry;
        use reduceRight = proc(rx,y) 
            ry := [reduce(y)];
            # rx could be an expseq
            if [rx]::list(Static) and ry::list(Static) then
                oper(rx,op(ry));
            else
                f(embed(rx), embed(op(ry)));
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
        `if`(env:-hasNargs(), env:-getArgs(), MArgs()); 
    end proc;
    
    
    red[MCatenate] := proc(x,y) local r, h, n;
        r := reduce(y);
        if r::Dynamic then
            return MCatenate(x, r);
        end if;

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

        op(map(curry(`||`, FromInert(n)), [r]));
    end proc;

    red[MExpSeq] := proc() local rs;
        rs := map(reduce, [args]);
        `if`(rs::list(Static), op(rs), MExpSeq(op(map(embed, rs))))
    end proc;

    red[MList] := proc(eseq) local r;
        r := [reduce(eseq)];
        `if`(r::list(Static), r, MList(op(r)))
    end proc;

    red[MSet] := proc(eseq) local r;
        r := reduce(eseq);
        `if`([r]::list(Static), {r}, MSet(r));
    end proc;

    red[MMember] := proc(x1, x2) local rx1, rx2;
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
    
    
    specFunc["print"] := proc(expseq)
        return MFunction(M:-ProtectedForm("print"), embed(reduce(expseq)));
    end proc;
    
    # TODO, this is not correct, because support for evaln is not there yet
    specFunc["assigned"] := proc(expseq) local val, rindex, var, index;
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
        elif typematch(val, MTableref('var'::mform, 'index'::mform)) then
            
            rindex := reduce(index);
            
#            if val = MTableref(MParam("D"), MExpSeq(MParam("operation"))) then
#                print("found it man!");
#                print("result: ", env:-isTblValAssigned(Name(var), rindex));
#                print("rindex", [rindex]);
#                print();
#            end if;    
#            
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
    
    
    specFunc["seq"] := proc(expseq) local m;
        m := MFunction( M:-ProtectedForm("seq"), MExpSeq(op(map(embed, [reduce(expseq)]))) );
        # eval(FromInert(M:-FromM(m)));
        FromInert(M:-FromM(m));
    end proc;
    
    specFunc["if"] := proc(expseq) local m;
        m := MFunction( M:-ProtectedForm("if"), MExpSeq(op(map(embed, [reduce(expseq)]))) );
        # eval(FromInert(M:-FromM(m)));
        FromInert(M:-FromM(m));
    end proc;
    
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
    # know that both args are static
    red[MTableref] := proc(tbl, eseq) local re, rt, val, h;
        re := reduce(eseq);
        if Header(tbl) = MArgs then
            if env:-hasArgsVal(re) then
                return env:-getArgsVal(re)
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
                    if not env:-isStaticVal(Name(tbl)) then
                        return MTableref(tbl, embed(re));
                    end if;
                end try;
            elif member(h, {MName, MAssignedName}) then
                try
                    return genv:-getTblVal(Name(tbl), re);
                catch "table value is dynamic" : # fall through
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

    reduceName := f -> proc(n) local hasDyn, c;
        if not assigned(genv) or genv:-isDynamic(n) then
            (c-> `if`(type(c, 'last_name_eval'), c, eval(c)))(convert(n,'name'));
        else
            `if`(hasDyn and treatAsDynamic, f(n), 
                genv:-getVal(n, 'hasDyn') );
        end if
    end proc;
    
    reduceVar := proc(x) local hasDyn, val;
        if env:-isStatic(x) then
            val := env:-getVal(x, 'hasDyn');
            #`if`(hasDyn and treatAsDynamic, f(x), val);
            if hasDyn and treatAsDynamic then
                return __F(x);
            end if;
            if type(val, name) and genv:-isStatic(convert(val, string)) then
                val := genv:-getVal(convert(val,string), 'hasDyn');
                if hasDyn and treatAsDynamic then
                    return __F(x);
                else
                    return val;
                end if;
            end if;
            eval(val,1);
        else
            __F(x);
        end if;
    end proc;

    # these evals are needed to get at the actual proc generated
    # they make debugging easier
    red[MParam]     := subs(__F=MParam, eval(reduceVar));
    red[MLocal]     := subs(__F=MLocal, eval(reduceVar));
    red[MSingleUse] := subs(__F=MSingleUse, eval(reduceVar));
    red[MGeneratedName] := subs(__F=MGeneratedName, eval(reduceVar));

    red[MLexicalLocal] := reduceLex(MLexicalLocal);
    red[MLexicalParam] := reduceLex(MLexicalParam);

    reduceLex := f -> proc(x) local lex;
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

    red[MLocalName] := proc()
        FromInert(M:-FromM(MLocalName(args)));
    end proc;
    
    # a closure is created
    red[MProc] := proc() local p, thunk, lexMap, newBody, newProc;
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

    replaceClosureLexical := proc(lexMap, n) local closureEnv, s, lookup, thunk;
        closureEnv := callStack:-topEnv();
        s := op(n);
        lookup := proc() local lex, lexName;
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
        
        thunk := proc() lookup() end proc;        
        thunk := setattribute(eval(thunk,2), 'pe_thunk'); # used to identify these thunks later
        
        MFunction(MStatic(thunk), MExpSeq());        
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
            #MUneval(embed(e));
            #error "local uneval not supported yet";
        else
            error "dynamic uneval not supported";
            MUneval(embed(e));
        end if;
    end proc;


end module;
