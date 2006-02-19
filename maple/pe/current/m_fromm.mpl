
FromM := module()
    export 
        ModuleApply;
    local 
        inrt, mtoi, mtoi2, mapmtoi,
        createParamMap, createLocalMappingFunctions, replaceLexical,
        singleAssigns, mapStack;

    inrt := table();
    mtoi, mtoi2, mapmtoi := createTableProcs("FromM", inrt);

    
    ModuleApply := proc(code::mform) local res;
        singleAssigns := table();
        mapStack := SimpleStack();
        res := mtoi(code);
        singleAssigns := 'singleAssigns';
        mapStack := 'mapStack';
        res;
    end proc;


    # returns a table that maps param names to their indices
    createParamMap := proc(paramseq) local f, tbl;
        f := proc(tbl, i, param)
            tbl[op(1,param)] := i
        end proc;
        tbl := createMap(paramseq, f);
        x -> tbl[x];
    end proc;


    # returns two functions used to generate locals
 	createLocalMappingFunctions := proc() local tbl, q, c;
	    # contents of closure
	    tbl := table();
	    q := SimpleQueue();
	    c := 0;

        # procedure that replaces a local with its index
	    proc(x)
	        if not assigned(tbl[x]) then
     	        c := c + 1;
	            tbl[x] := c;
	            q:-enqueue(_Inert_NAME(x));
	            c;
	        else
	            tbl[x];
	        end if;
	    end proc,

	    # procedure that creates a new local sequence
	    () -> _Inert_LOCALSEQ(qtoseq(q));
	end proc;


    inrt['string']  := () -> args;
    inrt['Integer'] := () -> args;
    
    inrt[MStatic] := proc()
        if nargs = 1 then
            _Inert_VERBATIM(args);
        else
            error "MStatic should only contain one operand";
        end if;
    end proc;
    
    inrt[MBoth] := proc(s, d)
        mtoi(d);
    end proc;
    
    
    inrt[MarkedLambda] := proc()
        print("MarkedLambda", args);
        error "(FromM) MarkedLambda should have been removed by ToM";
    end proc;

    
    inrt[MParam]     := n -> _Inert_PARAM(mapStack:-top()['params'](n));
    inrt[MLocal]     := n -> _Inert_LOCAL(mapStack:-top()['locals'](n));
    inrt[MLocalName]         := _Inert_LOCALNAME @ mapmtoi;
    inrt[MAssignedLocalName] := _Inert_ASSIGNEDLOCALNAME @ mapmtoi;

    inrt[MName]         := _Inert_NAME @ mapmtoi;
    inrt[MAssignedName] := _Inert_ASSIGNEDNAME @ mapmtoi;

    inrt[MMember]    := _Inert_MEMBER    @ mapmtoi;
    inrt[MAttribute] := _Inert_ATTRIBUTE @ mapmtoi;

    inrt[MInt] := x -> `if`(x < 0, _Inert_INTNEG(-x), _Inert_INTPOS(x));
    inrt[MString] := _Inert_STRING;

    inrt[MNot] := _Inert_NOT @ mtoi;

    inrt[MFloat]    := _Inert_FLOAT    @ mtoi2;
    inrt[MEquation] := _Inert_EQUATION @ mtoi2;
    inrt[MPower]    := _Inert_POWER    @ mtoi2;
    inrt[MCatenate] := _Inert_CATENATE @ mtoi2;
    inrt[MLesseq]   := _Inert_LESSEQ   @ mtoi2;
    inrt[MLessThan] := _Inert_LESSTHAN @ mtoi2;
    inrt[MImplies]  := _Inert_IMPLIES  @ mtoi2;
    inrt[MAnd]      := _Inert_AND      @ mtoi2;
    inrt[MOr]       := _Inert_OR       @ mtoi2;
    inrt[MXor]      := _Inert_XOR      @ mtoi2;

    inrt[MRational] := _Inert_RATIONAL @ mtoi2;
    inrt[MComplex]  := _Inert_COMPLEX  @ mtoi2;

    inrt[MList] := _Inert_LIST @ mapmtoi;
    inrt[MSet]  := _Inert_SET  @ mapmtoi;

    inrt[MExpSeq] := _Inert_EXPSEQ @ mapmtoi;
    inrt[MSum]    := _Inert_SUM    @ mapmtoi;
    inrt[MProd]   := _Inert_PROD   @ mapmtoi;

    inrt[MArgs]     := _Inert_ARGS     @ mapmtoi;
    inrt[MNargs]    := _Inert_NARGS    @ mapmtoi;

    inrt[MReturn]  := _Inert_RETURN  @ mapmtoi;
    inrt[MError]   := _Inert_ERROR   @ mapmtoi;
    inrt[MUneval]  := _Inert_UNEVAL  @ mapmtoi;
    inrt[MRange]   := _Inert_RANGE   @ mapmtoi;
    inrt[MInequat] := _Inert_INEQUAT @ mapmtoi;
    

    inrt[MParamSeq]       := _Inert_PARAMSEQ       @ mapmtoi;
    inrt[MLocalSeq]       := _Inert_LOCALSEQ       @ mapmtoi;
    inrt[MOptionSeq]      := _Inert_OPTIONSEQ      @ mapmtoi;
    inrt[MDescriptionSeq] := _Inert_DESCRIPTIONSEQ @ mapmtoi;
    inrt[MGlobalSeq]      := _Inert_GLOBALSEQ      @ mapmtoi;
    inrt[MLexicalPair]    := _Inert_LEXICALPAIR    @ mapmtoi;

    inrt[MEop]   := _Inert_EOP            @ mapmtoi;
    inrt[MFlags] := NULL;

    inrt[MStandaloneExpr] := mapmtoi;

    inrt[MStatSeq]            := _Inert_STATSEQ  @ mapmtoi;
    inrt[MAssign]             := _Inert_ASSIGN   @ mapmtoi;
    inrt[MAssignToFunction]   := _Inert_ASSIGN   @ mapmtoi;
    inrt[MTableAssign]        := _Inert_ASSIGN   @ mapmtoi;
        
    inrt[MWhileForIn]   := _Inert_FORIN   @ mapmtoi;
    inrt[MWhileForFrom] := _Inert_FORFROM @ mapmtoi;
    
    inrt[MCommand] := proc(n)
        _Inert_FUNCTION(_Inert_NAME("&onpe"), _Inert_EXPSEQ(_Inert_STRING(n)));
    end proc;
    
    inrt[MParamSpec] := proc(n, t, d) # name, type, default
        local param;
        param := _Inert_NAME(n);
        if nops(t) > 0 then
            param := _Inert_DCOLON(param, ToInert(op(t)));
        end if;
        if nops(d) > 0 then
            param := _Inert_ASSIGN(param, mtoi(op(d)));
        end if;
        param;
    end proc;
    
    
    inrt[MKeywords] := proc()
        _Inert_SET(_Inert_EXPSEQ(mapmtoi(args)));
    end proc;
    
    
    # TODO, should MStandaloneFunction be similiar?
    inrt[MFunction] := proc(n, expseq)
        _Inert_FUNCTION(mtoi(n), _Inert_EXPSEQ(mtoi(expseq)));
    end proc;
    
    
    inrt[MTableref] := proc(t, expseq)
        _Inert_TABLEREF(mtoi(t), _Inert_EXPSEQ(mtoi(expseq)));
    end proc;
    
    
    inrt[MStandaloneFunction] := inrt[MFunction];
    
    inrt[MForFrom] := proc(loopVar, fromExp, byExp, toExp, statseq)
        _Inert_FORFROM(mapmtoi(loopVar, fromExp, byExp, toExp), inertTrue, mtoi(statseq));
    end proc;
    
    inrt[MForIn] := proc(loopVar, inExp, whileExp, statseq)
        if nargs = 3 then
            _Inert_FORIN(mtoi(loopVar), mtoi(inExp), inertTrue, _Inert_STATSEQ(_Inert_EXPSEQ()));
        else
            _Inert_FORIN(mtoi(loopVar), mtoi(inExp), inertTrue, mtoi(statseq));
        end if;
    end proc;
    
    inrt[MWhile] := proc(loopVar, fromExp, byExp, whileExp, statseq)
        _Inert_FORFROM(mapmtoi(loopVar, fromExp, byExp), _Inert_EXPSEQ(), mtoi(whileExp), mtoi(statseq));
    end proc;
    
    inrt[MProc] := proc() local maps, inertProc, pars, keys, newLocalList;
        maps := table();

        # function that maps param names to their indicies
        maps['params'] := createParamMap([args][1]);
        # first is a function that keeps track of locals encountered
        # second is a function that generates the new local list
        maps['locals'], newLocalList := createLocalMappingFunctions();
        # the current lexical sequence, which may become smaller
        maps['lexseq'] := CreateLexNameMap([args][8]);
        # queue that will become the new lexical sequence
        maps['lexqueue'] := SimpleQueue();
        # table mapping a lexical's name to its index in the lexical queue
        maps['lextbl'] := table();

        mapStack:-push(maps);

        inertProc := _Inert_PROC(mapmtoi(args));
        pars := op(1, inertProc);
        keys := op(10, inertProc); # keywords are at spot 10 because MFlags maps to NULL
        pars := _Inert_PARAMSEQ(op(pars), keys);
        
        mapStack:-pop();
        subsop(1=pars, 2=newLocalList(), 10=NULL, inertProc);
    end proc;


    inrt[MLexicalSeq] := proc() local lexQueue;
        lexQueue := mapStack:-top()['lexqueue'];
        _Inert_LEXICALSEQ(op(lexQueue:-toList()));
    end proc;

    replaceLexical := proc(f, m, n) 
        local maps, lexTbl, temp, index, lexpair, lexQueue;
        maps := mapStack:-top();
        lexTbl := maps['lextbl'];
        
        if assigned(lexTbl[n]) then
            lexTbl[n];
        else
            if mapStack:-depth() > 1 and f = _Inert_LOCAL then
                temp := mapStack:-pop();
				index := mapStack:-top()['locals'](n);
                mapStack:-push(temp);
                lexpair := _Inert_LEXICALPAIR(_Inert_NAME(n), _Inert_LOCAL(index));
            else
                if not assigned(maps['lexseq'][n]) then
                    error "lexical not found in lexical sequence", args;
                end if;
                lexpair := mtoi(maps['lexseq'][n]);
            end if;

            lexQueue := maps['lexqueue'];
            lexQueue:-enqueue(lexpair);
            index := lexQueue:-length();
            lexTbl[n] := index;
            index
        end if;
    end proc;

    inrt[MLexicalParam] := proc(n)
        _Inert_LEXICAL_PARAM(replaceLexical(_Inert_PARAM, 'params', n))
    end proc;

    inrt[MLexicalLocal] := proc(n)
        _Inert_LEXICAL_LOCAL(replaceLexical(_Inert_LOCAL, 'locals', n))
    end proc;


    inrt[MSingleAssign] := proc(n::mform({GeneratedName, SingleUse}), e::mform)
        singleAssigns[op(n)] := mtoi(e);
        NULL;
        #_Inert_ASSIGN(mapmtoi(args));
    end proc;

    inrt[MSingleUse] := proc(n)
        if assigned(singleAssigns[n]) then
            singleAssigns[n];
        else
            inrt[MLocal](n);
        end if;
    end proc;

    inrt[MGeneratedName] := inrt[MSingleUse];

    inrt[MIfThenElse] := proc(c, s1, s2)
        if IsNoOp(s1) and IsNoOp(s2) then
            _Inert_EXPSEQ();
        elif IsNoOp(s2) then
            _Inert_IF(_Inert_CONDPAIR(mtoi(c), mtoi(s1)));
        else
            _Inert_IF(_Inert_CONDPAIR(mtoi(c), mtoi(s1)), _Inert_STATSEQ(mtoi(s2)))
        end if;
    end proc;

    inrt[MTypedName] := proc(n::string, t::mform(Type))
        _Inert_DCOLON(_Inert_NAME(n), _Inert_VERBATIM(op(t)));
    end proc;

    inrt[MTry] := proc(t, catchseq, fin) local q, c;
        q := SimpleQueue();
        q:-enqueue(mtoi(t));
        for c in catchseq do
            q:-enqueue(mtoi(op(1,c)));
            q:-enqueue(mtoi(op(2,c)));
        end do;
        if nargs = 3 then # if there is a finally clause
            q:-enqueue(mtoi(op(fin)));
        end if;
        _Inert_TRY(qtoseq(q));
    end proc;

end module;
