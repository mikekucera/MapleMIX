ToM := module()
    export ModuleApply;
    local MapStack, isInertTrue,
    	  itom, itom2, mapitom,  m, gen, lamGen, getVar, knownNames;

    m := table();

    itom, itom2, mapitom := createTableProcs("ToM", m);

    gen := NameGenerator("m");
    lamGen := NameGenerator("lambda");
    
    ModuleApply := proc(x::inert)
    	MapStack := SimpleStack();
    	knownNames := table();
    	res := itom(x);
    	names := {op(map(op, [indices(knownNames)]))};
    	knownNames := 'knownNames';
		MapStack := 'MapStack';
		res, names;
    end proc;

    addName := proc(n)
        if assigned(knownNames) then
            knownNames[n] := NULL;
        end if;
    end proc;
    
    createParamMap := proc(varSeq)
        mapParam := proc(tbl,i,var)
            if var <> inertDollar then
                properOp := x -> op(`if`(Header(x)=_Inert_DCOLON, [1,1], 1) , x);     
                tbl[i] := properOp(`if`(Header(var)=_Inert_ASSIGN, op(1,var), var));
                addName(tbl[i]);
            end if
        end proc;
    
        createMap(varSeq,
            proc(tbl, i, var)
                if Header(var) = _Inert_SET then
                    index := i;
                    for x in op(var) do
                        mapParam(tbl, index, x);
                        index := index + 1;
                    end do;
                else
                    mapParam(tbl, i, var);
                end if;
            end proc)       
    end proc;
    
    createLocalMap := proc(varSeq)
        createMap(varSeq,
            proc(tbl, i, var)
                tbl[i] := Name(var);
                addName(Name(var));
            end proc)
    end proc;
    

    # maps lexical indicies to their names
    createLexIndexMap := proc(lexicalseq)
        createMap(lexicalseq,
            proc(tbl, i, lexpair)
                tbl[i] := op([1,1], lexpair)
            end proc)
    end proc;


    getVar := proc(mapname, x) 
        MapStack:-top()[mapname][x];
    end proc;
    
    getLexVar := x -> getVar('lex', x);


    isStandalone := proc(x) option inline;
        member(op(0,x),
            {_Inert_SUM, _Inert_PROD, _Inert_POWER, _Inert_CATENATE,
             _Inert_EQUATION, _Inert_LESSEQ, _Inert_LESSTHAN, _Inert_IMPLIES,
             _Inert_AND, _Inert_OR, _Inert_XOR, _Inert_NOT, _Inert_INTPOS,
             _Inert_INTNEG, _Inert_FLOAT, _Inert_STRING, _Inert_COMPLEX,
             _Inert_RATIONAL, _Inert_EXPSEQ, _Inert_LIST, _Inert_SET,
             _Inert_PARAM, _Inert_LOCAL, _Inert_NAME,
             _Inert_ASSIGNEDNAME, _Inert_TABLEREF,
             _Inert_MEMBER, _Inert_ARGS, _Inert_NARGS, _Inert_UNEVAL, _Inert_TABLE});
    end proc;

    # takes an inert expression and splits it
    splitAssigns := proc(e::inert)
        q := SimpleQueue();
        
        examineFunc := proc(f)
            local newvar;
            if member(convert(op(1,f), name), intrinsic) then
                MFunction(mapitom(args));
            else
                newvar := gen();
                addName(newvar);
                q:-enqueue(MAssignToFunction(MSingleUse(newvar), MFunction(mapitom(args))));
                MSingleUse(newvar);
            end if;
        end proc;
    
        doIt := proc(expr)
            h := Header(expr);
            if not type(expr, inert) or h = _Inert_PROC then
                expr;
            elif h = _Inert_FUNCTION then
                examineFunc(op(map(procname,expr)))
            else
                map(procname, expr);
            end if;
        end proc;
        # generation of assigns is a side effect of nested proc
        
        res := doIt(e);
        return q:-toList(), itom(res);
    end proc;


    # splits the given expression, then applies the continuation k to the stripped expression
    split := proc(expr, k)
        assigns, reduced := splitAssigns(expr);
        if nops(assigns) = 0 then
        	k(reduced);
        else
        	MStatSeq(op(assigns), k(reduced));
        end if;
    end proc;

    # version of split that returns the results instead of applying a continuation
    splitReturn := proc(expr)
        assigns, reduced := splitAssigns(expr);
        return MStatSeq(op(assigns)), reduced;
    end proc;


    m['string'] := () -> args;
    m['Integer'] := () -> args;
    m[MSingleUse] := MSingleUse;
    m[MProc] := MProc;
    m[MFunction] := MFunction;
    # MFunction is introduced prematurely by the expression splitter
    #m[MFunction] := MFunction @ mapitom;
    
    m[_Inert_NAME]     := MName @ mapitom;
    m[_Inert_LOCAL]    := x -> MLocal(getVar('locals', x));
    m[_Inert_PARAM]    := x -> MParam(getVar('params', x));

    m[_Inert_LEXICAL_LOCAL] := MLexicalLocal @ getLexVar;
    m[_Inert_LEXICAL_PARAM] := MLexicalParam @ getLexVar;
    m[_Inert_LEXICALPAIR]   := MLexicalPair  @ itom2;
    m[_Inert_LOCALNAME]     := MLocalName    @ mapitom;

    m[_Inert_ASSIGNEDNAME] := MAssignedName @ mapitom;
    m[_Inert_ASSIGNEDLOCALNAME] := MAssignedLocalName @ mapitom;

    m[_Inert_INTPOS]   := MInt;
    m[_Inert_INTNEG]   := MInt @ `-`;
    m[_Inert_STRING]   := MString;

    m[_Inert_NOT]      := MNot @ itom;

    m[_Inert_FLOAT]    := MFloat    @ itom2;
    m[_Inert_EQUATION] := MEquation @ itom2;
    m[_Inert_POWER]    := MPower    @ itom2;
    m[_Inert_CATENATE] := MCatenate @ itom2;
    m[_Inert_LESSEQ]   := MLesseq   @ itom2;
    m[_Inert_LESSTHAN] := MLessThan @ itom2;
    m[_Inert_IMPLIES]  := MImplies  @ itom2;
    m[_Inert_AND]      := MAnd      @ itom2;
    m[_Inert_OR]       := MOr       @ itom2;
    m[_Inert_XOR]      := MXor      @ itom2;

    m[_Inert_RATIONAL]  := MRational @ itom2;
    m[_Inert_COMPLEX]   := MComplex  @ itom2;

    m[_Inert_LIST]      := MList @ mapitom;
    m[_Inert_SET]       := MSet  @ mapitom;

    m[_Inert_EXPSEQ]    := MExpSeq @ mapitom;
    m[_Inert_SUM]       := MSum    @ mapitom;
    m[_Inert_PROD]      := MProd   @ mapitom;
    m[_Inert_ERROR]     := MError  @ mapitom;
    m[_Inert_TABLEREF]  := MTableref @ mapitom;
    m[_Inert_ARGS]      := MArgs @ mapitom;
    m[_Inert_NARGS]     := MNargs @ mapitom;
    m[_Inert_UNEVAL]    := MUneval @ mapitom;
    m[_Inert_RANGE]     := MRange @ mapitom;
    m[_Inert_INEQUAT]   := MInequat @ mapitom;    

    m[_Inert_MEMBER]    := MMember    @ mapitom;
    m[_Inert_ATTRIBUTE] := MAttribute @ mapitom;
    #m[_Inert_ATTRIBUTE] := () -> NULL;
    
    m[_Inert_LOCALSEQ]       := MLocalSeq       @ mapitom;
    m[_Inert_OPTIONSEQ]      := MOptionSeq      @ mapitom;
    m[_Inert_DESCRIPTIONSEQ] := MDescriptionSeq @ mapitom;
    m[_Inert_GLOBALSEQ]      := MGlobalSeq      @ mapitom;
    m[_Inert_EOP]            := MEop            @ mapitom;    
    #m[_Inert_PARAMSEQ]       := MParamSeq       @ mapitom;
    
    m[_Inert_PARAMSEQ]  := proc()       
        if nargs = 0 then
            return MParamSeq(), MKeywords();
        end if;
        
        paramq := SimpleQueue();
        keywordq := SimpleQueue();
        
        for arg in [args] do
            if arg = inertDollar then next end if;
            if Header(arg) = _Inert_SET then
                map(keywordq:-enqueue, map(paramSpec, [op(op(arg))]));
            else
                paramq:-enqueue(paramSpec(arg));
            end if;
        end do;
        
        MParamSeq(qtoseq(paramq)), MKeywords(qtoseq(keywordq));             
    end proc;
    
    paramSpec := proc(x)
        if hasfun(x, _Inert_PARAM) then
            error "referencing one parameter from another is not supported: %1", x;
        elif hasfun(x, _Inert_FUNCTION) then
            error "parameter expression cannot contain a function call: %1", x;
        end if;
        
        param := x;
        
        if Header(param) = _Inert_ASSIGN then
            d := MDefault(itom(op(2,param)));
            param := op(1,param);
        else
            d := MDefault();
        end if;
        if Header(param) = _Inert_DCOLON then
            n := op([1,1], param);
            t := MType(FromInert(op(2,param)));
        else
            n := op(1, param);
            t := MType();
        end if;
        
        if not type(n, string)  then
            error "unknown form in parameter sequence: %1", n
        end if;
        
        MParamSpec(n, t, d)
    end proc;
    
    
    m[_Inert_DCOLON] := proc(n, t)
        # TODO, the op(1,n) will strip off protected attributes, not sure if this is best
        MTypedName(op(1,n), MType(FromInert(t)));
    end proc;
    
    # remember tables are not considered
    m[_Inert_HASHTAB] := () -> MExpSeq();
    
    

    m[_Inert_TABLE] := proc(indexFcn, hashTab)
        if indexFcn <> _Inert_EXPSEQ() then
            error "custom indexing functions are not supported"
        end if;

        processHashPair := proc(pair)
            MEquation(itom(Fst(pair)), itom(Snd(pair)));
        end proc;
    
        lst := MList(MExpSeq(op(map(processHashPair, hashTab))));
        MFunction(ProtectedForm("table"), MExpSeq(lst));
    end proc;
    
    
    m[_Inert_FORFROM] := proc(loopVar, fromExp, byExp, toExp, whileExp, statseq)
        ss1, e1 := splitReturn(loopVar);
        ss2, e2 := splitReturn(fromExp);
        ss3, e3 := splitReturn(byExp);
        ss4, e4 := splitReturn(toExp);
        ss5, e5 := splitReturn(whileExp);

        body := RemoveNext(statseq);
        body := MStatSeq(itom(body), ssop(ss5));

        if toExp = _Inert_EXPSEQ() then # its a simple while loop
            loop := MWhile(e1, e2, e3, e5, body);
        elif whileExp = inertTrue then
            loop := MForFrom(e1, e2, e3, e4, body);
        else
            loop := MWhileForFrom(e1, e2, e3, e4, e5, body);
        end if;
        
        assigns := ssop(ss1), ssop(ss2), ssop(ss3), ssop(ss4), ssop(ss5);
        MStatSeq(assigns, loop);
    end proc;
    
    
    m[_Inert_FORIN] := proc(loopVar, inExp, whileExp, statseq)
        ss1, e1 := splitReturn(loopVar);
        ss2, e2 := splitReturn(inExp);
        ss3, e3 := splitReturn(whileExp);
        
        body := RemoveNext(statseq);
        body := MStatSeq(itom(body), ssop(ss3));
        
        if whileExp = inertTrue then
            loop := MForIn(e1, e2, body);
        else
            loop := MWhileForIn(e1, e2, e3, body);
        end if;
        
        MStatSeq(ssop(ss1), ssop(ss2), ssop(ss3), loop);
    end proc;    
    
    
    # removes a common usage of next in loops
    RemoveNext := proc(loopBody::inert(STATSEQ)) local c;
        num := nops(loopBody);
        for i from 1 to num do
            stmt := op(i, loopBody);
            if typematch(stmt, _Inert_IF(_Inert_CONDPAIR('c'::anything, _Inert_STATSEQ(_Inert_NEXT())))) then
                newIf := _Inert_IF(_Inert_CONDPAIR(_Inert_NOT(c), _Inert_STATSEQ(op(i+1..num, loopBody))));
                return _Inert_STATSEQ(op(1..i-1, loopBody), newIf);
            end if;
        end do;
        return loopBody;
    end proc;
    
    m[_Inert_NEXT] := proc()
        error "only very limited usage of next is supported";
    end proc;
    
    
    m[_Inert_PROC] := proc() local keys;
        maps := table();
        
        # $ in the parameter sequence throws the index of keywords off        
        ps := [args][1];
        if member(inertDollar, ps) and hasfun(ps, _Inert_SET) then
            front := [Front(ps)]; # the $ will be in the last position
            ps := _Inert_PARAMSEQ(Front(front), inertDollar, Last(front));            
        end if;
        
        maps['params'] := createParamMap(ps);        
        maps['locals'] := createLocalMap([args][2]);
        maps['lex']    := createLexIndexMap([args][8]);
        MapStack:-push(maps);
        
        pars, keys := m[_Inert_PARAMSEQ](op([args][1]));
        others := mapitom(args[2..-1]);
        flags := MFlags( MArgsFlag(UNKNOWN), MNargsFlag(UNKNOWN) );
        
        MProc(pars, others, flags, keys);
    end proc;

    # The lexical sequence comes after the proc body so its ok to pop the stacks
    # here. Actually its needed because the locals and params in the lexical
    # pairs refer to the outer environment.
    m[_Inert_LEXICALSEQ] := proc()
         MapStack:-pop();
         res := MLexicalSeq(mapitom(args));
    end proc;

    m[_Inert_STATSEQ] := proc() local standaloneExpr;
        processInert := proc(x)
            if Header(x) = _Inert_PROC then
                MStandaloneExpr(itom(x))
            elif isStandalone(x) then
                ssop(split(x, MStandaloneExpr))
            else
                ssop(itom(x));
            end if;
        end proc;
        MStatSeq(op(map(processInert, [args])));
    end proc;

    m[_Inert_FUNCTION] := proc(n, expseq)
        if op(1,n) = "&onpe" then
            if nops(expseq) = 0 then
                error "not enought arguments to command";
            end if;
            MCommand(op(map(Name, expseq)));
        elif member(convert(op(1,n), name), intrinsic) then
            split(expseq, x -> MStandaloneExpr(MFunction(itom(n), x)));
        else
            ss1, r1 := splitReturn(n);
            ss2, r2 := splitReturn(expseq);
            
            if nops(ss1) = 0 and nops(ss2) = 0 then
                MStandaloneFunction(r1, r2);
            else
                MStatSeq(ssop(ss1), ssop(ss2), MStandaloneFunction(r1, r2));
            end if;
        end if;
    end proc;

    


    # assumes splitter has already been run on tr
    splitTableRef := proc(tr::mform(Tableref))
        tbl := Tbl(tr);
        if Header(tbl) = MTableref then
            assigns, n := splitTableRef(tbl);
            newName := gen();
            addName(newName);
            new := MLocal(newName);
            [op(assigns), MAssign(new, MTableref(n, IndexExp(tr)))], new;
        else
            newName := gen();
            addName(newName);
            new := MLocal(newName);
            [MAssign(new, tr)], new;
        end if;
    end proc;
    

    m[_Inert_ASSIGN] := proc(target, expr)
        #in this case the assignment has multiple table refs on the left side that
        # must be split outp
        if Header(target) = _Inert_TABLEREF then
            assigns, splitTarget := splitReturn(target);
            if Header(Tbl(splitTarget)) = MTableref then
                moreAssigns, newName := splitTableRef(Tbl(splitTarget));
                MStatSeq(op(assigns), op(moreAssigns), 
                         split(expr, curry(MTableAssign, MTableref(newName, IndexExp(splitTarget)))));
            else
                MStatSeq(op(assigns), split(expr, curry(MTableAssign, splitTarget)));
            end if;
        else
            split(expr, curry(MAssign, itom(target)))
        end if;
    end proc;


    m[_Inert_RETURN] := e -> split(e, MReturn);

    m[_Inert_IF] := proc()
        if typematch([args], [_Inert_CONDPAIR('c'::anything, 's'::anything)]) then
            split(c, red -> MIfThenElse(red, MStatSeq(ssop(itom(s))), MStatSeq(MStandaloneExpr(MExpSeq()))));
        elif typematch([args], [_Inert_CONDPAIR('c'::anything, 's'::anything), 'el'::inert(STATSEQ)]) then
            split(c, red -> MIfThenElse(red, MStatSeq(ssop(itom(s))), MStatSeq(ssop(itom(el)))));
        else
            condpair := op(1, [args]);
            rest := op(2..-1, [args]);
            c, s := op(1, condpair), op(2, condpair);
            split(c, red -> MIfThenElse(red, MStatSeq(ssop(itom(s))), MStatSeq(itom(_Inert_IF(rest)))));
        end if;
    end proc;

    # converts a type assertion into a 'typed name'
    
    

    m[_Inert_TRY] := proc()
        catches := proc()
            bodies, strings := selectremove(type, [args], inert(STATSEQ));
            #strings, bodies := selectremove(type, [args], inert(STRING));
            f := (x,y) -> MCatch(itom(x), itom(y));
            (MCatchSeq @ op @ zip)(f, strings, bodies);
        end proc;

        fin := NULL;
        if nargs mod 2 = 0 then
            fin := MFinally(itom(args[nargs]));
        end if;

        MTry(itom(args[1]), catches(args[2..nargs]), fin);
    end proc;

end module: