# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.

ToM := module()
    export ModuleApply;
    local
        m, itom, itom2, mapitom, gen, lamGen, mapStack, knownNames,
        addName, createParamMap, createLocalMap, createLexIndexMap,
        createExportMap,
        getVar, getLexVar, isStandalone,
        splitAssigns, split, splitReturn, splitReturnMany, splitTableRef,
        nameGen,
        paramSpec, removeNext;

    m := table();

    itom, itom2, mapitom := createTableProcs("ToM", m);

    gen := NameGenerator("m");
    lamGen := NameGenerator("lambda");

    ModuleApply := proc(x::inert) local res, names;
    	mapStack := SimpleStack();
    	knownNames := table();
    	res := itom(x);
    	names := {op(map(op, [indices(knownNames)]))};
    	knownNames := 'knownNames';
		mapStack := 'mapStack';
		res, names;
    end proc;

    addName := proc(n)
        if assigned(knownNames) then
            knownNames[n] := NULL;
        end if;
        NULL;
    end proc;

    createParamMap := proc(varSeq) local mapParam;
        mapParam := proc(tbl,i,var) local properOp;
            if var <> inertDollar then
                properOp := x -> op(`if`(Header(x)=_Inert_DCOLON, [1,1], 1) , x);
                tbl[i] := properOp(`if`(Header(var)=_Inert_ASSIGN, op(1,var), var));
                addName(tbl[i]);
            end if
        end proc;

        createMap(varSeq,
            proc(tbl, i, var) local index, x;
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

    # completely copied on createLocalMap
    createExportMap := proc(varSeq)
        createMap(varSeq,
            proc(tbl, i, var)
                tbl[i] := Name(var);
                addName(Name(var));
            end proc)
    end proc;

    getVar := proc(mapname, x)
        mapStack:-top()[mapname][x];
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
             _Inert_ASSIGNEDNAME, _Inert_TABLEREF, _Inert_PROCNAME,
             _Inert_MEMBER, _Inert_ARGS, _Inert_NARGS, _Inert_UNEVAL, 
             _Inert_TABLE});
    end proc;

    # default name generator
    nameGen := proc() local newvar;
        newvar := gen();
        addName(newvar);
        newvar;
    end proc;

    # takes an inert expression and splits it
    # nam is an (optional) assignable object which we use as a name if present
    splitAssigns := proc(e::inert, nam := false )
        local q, post, examineFunc, doIt, res;
        q := SimpleQueue();
        post := SimpleQueue();

        examineFunc := proc(f,x) 
            local newvar, eqnToAssign, ee, resid, stat, ff;
            if nops(f) > 0 and isIntrinsic(Name(f)) then
                # catch a call to 'table' here
                if Name(f) = "table" and nargs>1 and
                    typematch(x, _Inert_EXPSEQ(_Inert_LIST('ee'::anything))) then
                    # at this point, x is a list initializer, ee its contents
                    # we still need to map itom onto that

                    # two different cases depending on whether we have
                    # a name or we're not at the top.  
                    # First, we have no good name
                    if nam::truefalse or not _EnvSplitAssignsTop then
                        ff := itom(ee);
                        if andmap(x -> evalb(Header(x) = MEquation), ff) then
                            # algo:
                            # 1. create a new name
                            # 2. associate it (first) to a table newvar 
                            #    [with static entries filled-in]
                            # 3. return eval(newvar,2)
                            # 4. after that, assign the dynamic entries
                            newvar := MLocal(nameGen());
                            resid, stat := selectremove(x->type(Snd(x),Dynamic),ff);
                            eqnToAssign := proc(eqn)
                                    post:-enqueue(MAssignTableIndex(MTableref(newvar, Fst(eqn)), Snd(eqn)));
                            end proc;
                            q:-enqueue(MAssign(newvar, MFunction(itom(f),stat)));
                            map(eqnToAssign, resid);
                            MFunction(MAssignedName("eval", "PROC"), MExpSeq(newvar,MInt(2)));
                        else
                            MFunction(mapitom(args));
                        end if;
                    else # and now we do have a name, and we are at the top
                        ff := itom(ee);
                        if andmap(x -> evalb(Header(x) = MEquation), ff) then
                            # algo:
                            # 1. use the already known name
                            # 2. associate to it the static entries
                            # 3. return that table
                            # 4. after that, assign the dynamic entries
                            newvar := nam;
                            resid, stat := selectremove(x->type(Snd(x),Dynamic),ff);
                            eqnToAssign := proc(eqn)
                                    post:-enqueue(MAssignTableIndex(MTableref(newvar, Fst(eqn)), Snd(eqn)));
                            end proc;
                            map(eqnToAssign, resid);
                            MFunction(itom(f),stat);
                        else
                            MFunction(mapitom(args));
                        end if;
                    end if;
                else
                    MFunction(mapitom(args));
                end if;
            else
                newvar := nameGen();
                q:-enqueue(MAssignToFunction(MSingleUse(newvar), MFunction(mapitom(args))));
                MSingleUse(newvar);
            end if;
        end proc;

        doIt := proc(expr) local h, t, o;
            h := Header(expr);
            if not type(expr, inert) or h = _Inert_PROC then
                expr;
            elif h = _Inert_FUNCTION then
                o := _EnvSplitAssignsTop;
                _EnvSplitAssignsTop := false;
                t := map(procname,expr);
                _EnvSplitAssignsTop := o;
                examineFunc(op(t));
            else
                _EnvSplitAssignsTop := false;
                map(procname, expr, false);
            end if;
        end proc;
        # generation of assigns is a side effect of nested proc

        _EnvSplitAssignsTop := true; # used to know if at stat level
        res := doIt(e);
        return q:-toList(), itom(res), post:-toList();
    end proc;

    # splits the given expression, then applies the continuation k to 
    # the stripped expression.  Passes any extra parameters on to
    # splitAssigns
    # Note that this should ONLY ever be called in a 'statement'
    # context, ie expr is top-level so that returning a MStatSeq is
    # always OK
    split := proc(expr, k) local pre_assigns, post_assigns, reduced;
        pre_assigns, reduced, post_assigns := splitAssigns(expr, args[3..-1]);
        if nops(pre_assigns) + nops(post_assigns) = 0 then
        	k(reduced);
        else
        	MStatSeq(op(pre_assigns), k(reduced), op(post_assigns));
        end if;
    end proc;

    # version of split that returns the results instead of applying a continuation
    splitReturn := proc(expr) local pre_assigns, post_assigns, reduced;
        pre_assigns, reduced, post_assigns := splitAssigns(expr);
        return MStatSeq(op(pre_assigns)), reduced, MStatSeq(op(post_assigns));
    end proc;

    # calls splitReturn on each argument, which returns a single MStatSeq of all
    # the assigns and an array of all the expressions
    splitReturnMany := proc() local pre_assigns, post_assigns, exprs, n, i;
        n := nargs;
        (pre_assigns, exprs, post_assigns) := (Array(1..n), Array(1..n), Array(1..n));
        for i from 1 to n do
            pre_assigns[i], exprs[i], post_assigns[i] := 
                splitReturn(args[i]);
        end do;
        # assigns, exprs := selectremove(x -> evalb(Header(x) = MStatSeq), map(splitReturn, [args]));
        pre_assigns, exprs, post_assigns;
    end proc;
    
    
    m['string'] := () -> args;
    m['Integer'] := () -> args;
    m[MSingleUse] := MSingleUse;
    m[MProc] := MProc;
    m[MFunction] := MFunction;
    m[MLocal] := MLocal;

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
    m[_Inert_FLOAT]    := MFloat @ itom2;

    m[_Inert_NOT] := MNot @ itom;

    m[_Inert_ARGS]  := MArgs;
    m[_Inert_NARGS] := MNargs;
    m[_Inert_PROCNAME] := MProcname;

    m[_Inert_EQUATION] := MEquation @ itom2;
    m[_Inert_INEQUAT]  := MInequat  @ itom2;
    m[_Inert_POWER]    := MPower    @ itom2;
    m[_Inert_CATENATE] := MCatenate @ itom2;
    m[_Inert_LESSEQ]   := MLesseq   @ itom2;
    m[_Inert_LESSTHAN] := MLessThan @ itom2;
    m[_Inert_IMPLIES]  := MImplies  @ itom2;
    m[_Inert_AND]      := MAnd      @ itom2;
    m[_Inert_OR]       := MOr       @ itom2;
    m[_Inert_XOR]      := MXor      @ itom2;
    m[_Inert_RATIONAL] := MRational @ itom2;
    m[_Inert_COMPLEX]  := MComplex  @ itom2;
    m[_Inert_RANGE]    := MRange    @ itom2;

    m[_Inert_LIST]      := MList @ mapitom;
    m[_Inert_SET]       := MSet  @ mapitom;

    m[_Inert_EXPSEQ]    := MExpSeq   @ mapitom;
    m[_Inert_SUM]       := MSum      @ mapitom;
    m[_Inert_PROD]      := MProd     @ mapitom;
    m[_Inert_TABLEREF]  := MTableref @ mapitom;
    m[_Inert_UNEVAL]    := MUneval   @ mapitom;

    m[_Inert_DCOLON]    := MDColon   @ mapitom;

    m[_Inert_MEMBER]    := MMember    @ mapitom;
    m[_Inert_ATTRIBUTE] := MAttribute @ mapitom; # TODO

    m[_Inert_LOCALSEQ]       := MLocalSeq       @ mapitom;
    m[_Inert_OPTIONSEQ]      := MOptionSeq      @ mapitom;
    m[_Inert_DESCRIPTIONSEQ] := MDescriptionSeq @ mapitom;
    m[_Inert_GLOBALSEQ]      := MGlobalSeq      @ mapitom;
    m[_Inert_EXPORTSEQ]      := MExportSeq      @ mapitom;
    m[_Inert_EOP]            := MEop            @ mapitom;

    m[_Inert_RETURN] := e -> split(e, MReturn);
    m[_Inert_ERROR]  := e -> split(e, MError);

    m[_Inert_PARAMSEQ]  := proc() local arg, paramq, keywordq;
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


    paramSpec := proc(x) local param, d, n, t;
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

    # "remember tables" are not dealt with at all
    # note that this might change the semantics, so this might need to 
    # change [ie throw an error instead of silently make it go away]
    m[_Inert_HASHTAB] := () -> MExpSeq();


    m[_Inert_TABLE] := proc(indexFcn, hashTab) local processHashPair, lst;
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
        local pre_assigns, post_assigns, exprs, body, loop, i;
        pre_assigns, exprs, post_assigns := splitReturnMany(loopVar, fromExp, byExp, toExp, whileExp);
        if post_assigns[5] <> MStatSeq() then
            error "cannot handle post-assignments in while condition";
        end if;
        body := MStatSeq(itom(removeNext(statseq)), ssop(pre_assigns[5]));

        if loopVar = _Inert_EXPSEQ() then
            exprs[1] := MLoopVar(gen("loopVar"));
        end if;
        
        if exprs[4] = _Inert_EXPSEQ() then # if the to expr is NULL then its a simple while loop
            loop := MWhile(exprs[5], body);
        elif whileExp = inertTrue then
            loop := MWhileForFrom(seq(exprs[i], i=1..4), MStatic(true), body);
        else
            loop := MWhileForFrom(seq(exprs[i], i=1..5), body);
        end if;

        MStatSeq(seq(ssop(pre_assigns[i]), i=1..5), loop, seq(ssop(post_assigns[i]),i=1..5));
    end proc;


    m[_Inert_FORIN] := proc(loopVar, inExp, whileExp, statseq)
        local pre_assigns, post_assigns, exprs, body, loop, e3;
        
        pre_assigns, exprs, post_assigns := splitReturnMany(loopVar, inExp, whileExp);
        
        if loopVar = _Inert_EXPSEQ() then
            exprs[1] := MLoopVar(gen("loopVar"));
        end if;
        
        body := MStatSeq(itom(removeNext(statseq)), ssop(pre_assigns[3]), ssop(post_assigns[3]));
        e3 := `if`(whileExp = inertTrue, MStatic(true), exprs[3]);
        loop := MWhileForIn(exprs[1], exprs[2], e3, body);
        MStatSeq(seq(ssop(pre_assigns[i]), i=1..3), loop, seq(ssop(post_assigns[i]), i=1..3));
    end proc;
    
    # removes a common usage of next in loops
    removeNext := proc(loopBody::inert(STATSEQ)) local num, i, stmt, newIf, c;
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

    m[_Inert_BREAK] := proc()
        error "the break keyword is not supported";
    end proc;


    m[_Inert_PROC] := proc() local maps, ps, front, pars, keys, others, flags;
        # $ in the parameter sequence throws the index of keywords off
        ps := [args][1];
        if member(inertDollar, ps) and hasfun(ps, _Inert_SET) then
            front := [Front(ps)]; # the $ will be in the last position
            ps := _Inert_PARAMSEQ(Front(front), inertDollar, Last(front));
        end if;

        maps := table();
        maps['params'] := createParamMap(ps);
        maps['locals'] := createLocalMap([args][2]);
        maps['lex']    := createLexIndexMap([args][8]);
        mapStack:-push(maps);

        pars, keys := m[_Inert_PARAMSEQ](op([args][1]));
        others := mapitom(args[2..-1]);
        flags := MFlags( MArgsFlag(UNKNOWN), MNargsFlag(UNKNOWN) );

        MProc(pars, others, flags, keys);
    end proc;

    # The lexical sequence comes after the proc body so its ok to pop the stacks
    # here. Actually its needed because the locals and params in the lexical
    # pairs refer to the outer environment.
    m[_Inert_LEXICALSEQ] := proc()
         mapStack:-pop();
         MLexicalSeq(mapitom(args));
    end proc;

    m[_Inert_STATSEQ] := proc() local processInert;
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
        local ss1, ss2, ss3, ss4, r1, r2;
        if Name(n) = "&onpe" then
            if nops(expseq) = 0 then
                error "not enought arguments to command";
            end if;
            MCommand(op(map(Name, expseq)));
        elif isIntrinsic(Name(n)) then
            split(expseq, x -> MStandaloneExpr(MFunction(itom(n), x)));
        else
            #split(_Inert_FUNCTION(n, expseq), MStandaloneExpr);
            ss1, r1, ss3 := splitReturn(n);
            ss2, r2, ss4 := splitReturn(expseq);

            MStatSeq(ssop(ss1), ssop(ss2), MStandaloneFunction(r1, r2),
                     ssop(ss3), ssop(ss4));
        end if;
    end proc;


    # MAssignToTable is a special M-form used to handle the case where 
    # a multi-dimensional table reference is used as an lvalue.
	# For example
	#   T[1][2] := x;
	# becomes
	#   m1 := T[1];
	#   m1[2] := x
    # Assumes splitter has already been run on tr.
    splitTableRef := proc(tr::mform(Tableref)) local tbl, assigns, n, newName, new;
        tbl := Tbl(tr);
        if Header(tbl) = MTableref then
            assigns, n := splitTableRef(tbl);
            newName := gen();
            addName(newName);
            new := MLocal(newName);
            [op(assigns), MAssignToTable(new, MTableref(n, IndexExp(tr)))], new;
        else
            newName := gen();
            addName(newName);
            new := MLocal(newName);
            [MAssignToTable(new, tr)], new;
        end if;
    end proc;


    m[_Inert_ASSIGN] := proc(target, expr) 
        local pre_assigns, post_assigns, splitTarget, moreAssigns, newName, splitExp, expseq, eqnToAssign;
        #in this case the assignment has multiple table refs on the left side that
        # must be split up
        if Header(target) = _Inert_TABLEREF then
            pre_assigns, splitTarget, post_assigns := splitReturn(target);
            if Header(Tbl(splitTarget)) = MTableref then
                moreAssigns, newName := splitTableRef(Tbl(splitTarget));
                MStatSeq(op(pre_assigns), op(moreAssigns),
                         split(expr, curry(MAssignTableIndex, MTableref(newName, IndexExp(splitTarget)))), post_assigns);
            else
                MStatSeq(op(pre_assigns), split(expr, curry(MAssignTableIndex, splitTarget)), op(post_assigns));
            end if;
        elif false and Header(expr) = _Inert_FUNCTION 
        and  op(1, expr) = _Inert_ASSIGNEDNAME("table", "PROC", _Inert_ATTRIBUTE(_Inert_NAME("protected", _Inert_ATTRIBUTE(_Inert_NAME("protected"))))) 
        and  nops(op(2,expr))>0 and Header(op([2,1], expr)) = _Inert_LIST then
            pre_assigns, splitExp, post_assigns := splitReturn(expr);
            expseq := op([2,1,1], splitExp);
            if andmap(x -> evalb(Header(x) = MEquation), expseq) then
                eqnToAssign := proc(eqn)
                    MAssignTableIndex(MTableref(itom(target), Fst(eqn)), Snd(eqn));
                end proc;
                MStatSeq(op(pre_assigns), op(map(eqnToAssign, expseq)), MStandaloneExpr(itom(target)), op(post_assigns));
            else
                split(expr, curry(MAssign, itom(target)))
            end if;
        else
            split(expr, curry(MAssign, itom(target)), itom(target))
        end if;
    end proc;


    m[_Inert_IF] := proc() local condpair, rest, c, s, el;
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


    m[_Inert_TRY] := proc() local catches, fin;
        catches := proc() local bodies, strings, f;
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

    # placeholder for now, to see what's needed
    m[_Inert_MODULE] := proc()
        MModule(mapitom(args));
    end proc;

    m[_Inert_MODDEF] := proc() local maps, ps, front, pars, keys, others, flags;
        # $ in the parameter sequence throws the index of keywords off
        ps := [args][1];
        if member(inertDollar, ps) and hasfun(ps, _Inert_SET) then
            front := [Front(ps)]; # the $ will be in the last position
            ps := _Inert_PARAMSEQ(Front(front), inertDollar, Last(front));
        end if;

        maps := table();
        maps['params'] := createParamMap(ps);
        maps['locals'] := createLocalMap([args][2]);
        maps['lex']    := createLexIndexMap([args][8]);
        maps['exprt']  := createExportMap([args][4]);
        mapStack:-push(maps);

        pars, keys := m[_Inert_PARAMSEQ](op([args][1]));
        others := mapitom(args[2..-1]);
        flags := MFlags( MArgsFlag(UNKNOWN), MNargsFlag(UNKNOWN) );

        MModDef(pars, others, flags, keys);
    end proc;

end module:
