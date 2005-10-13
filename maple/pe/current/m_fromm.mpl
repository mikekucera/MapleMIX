
FromM := module()
    export ModuleApply;
    local i, mtoi, mtoi2, mapmtoi, createParamMap, paramMap, singleAssigns,
          createLocalMappingFunctions, replaceLocal, newLocalList;

    i := table();
    mtoi, mtoi2, mapmtoi := createTableProcs(i);

    ModuleApply := proc(code::m(Proc))
        singleAssigns := table();
        paramMap := createParamMap(Params(code));        
        replaceLocal, newLocalList := createLocalMappingFunctions();        
        inertProc := mtoi(code);
        singleAssigns := 'singleAssigns';
        subsop(2=newLocalList(), inertProc);
    end proc;
    
    
    # returns a table that maps param names to their indices
    createParamMap := proc(params)
        local tbl, param, index;
        tbl := table();
        index := 1;
        for param in params do
            tbl[op(1, param)] := index;
            index := index + 1;
        end do;
        tbl;
    end proc;


    # returns two functions used to generate locals
 	createLocalMappingFunctions := proc()
	    local tbl, q, c;	    
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
	    () -> _Inert_LOCALSEQ(op(q:-toList()));
	end proc;

    
    i[MName]      := _Inert_NAME;    
    i[MParam]     := n -> _Inert_PARAM(paramMap[n]);
    
    i[MLocal]     := n -> _Inert_LOCAL(replaceLocal(n));    
    i[MGeneratedName] := i[MLocal];

    i[MAssignedName] := _Inert_ASSIGNEDNAME;
    
    i[MInt] := x -> `if`(x < 0, _Inert_INTNEG(-x), _Inert_INTPOS(x));
    i[MString] := _Inert_STRING;
    
    i[MNot] := _Inert_NOT @ mtoi;
    
    i[MFloat]    := _Inert_FLOAT    @ mtoi2;
    i[MEquation] := _Inert_EQUATION @ mtoi2;
    i[MPower]    := _Inert_POWER    @ mtoi2;
    i[MCatenate] := _Inert_CATENATE @ mtoi2;
    i[MLesseq]   := _Inert_LESSEQ   @ mtoi2;
    i[MLessThan] := _Inert_LESSTHAN @ mtoi2;
    i[MImplies]  := _Inert_IMPLIES  @ mtoi2;
    i[MAnd]      := _Inert_AND      @ mtoi2;
    i[MOr]       := _Inert_OR       @ mtoi2;
    i[MXor]      := _Inert_XOR      @ mtoi2;
    
    i[MRational] := _Inert_RATIONAL @ mtoi2;
    i[MComplex]  := _Inert_COMPLEX  @ mtoi2;
    
    i[MList] := _Inert_LIST @ mapmtoi;
    i[MSet]  := _Inert_SET  @ mapmtoi;
    
    i[MExpSeq] := _Inert_EXPSEQ @ mapmtoi; 
    i[MSum]    := _Inert_SUM    @ mapmtoi;
    i[MProd]   := _Inert_PROD   @ mapmtoi;
    
    i[MReturn] := _Inert_RETURN @ mapmtoi;
    
    i[MProc]           := _Inert_PROC           @ mapmtoi;
    i[MParamSeq]       := _Inert_PARAMSEQ       @ mapmtoi;
    i[MLocalSeq]       := _Inert_LOCALSEQ       @ mapmtoi;
    i[MOptionSeq]      := _Inert_OPTIONSEQ      @ mapmtoi;
    i[MDescriptionSeq] := _Inert_DESCRIPTIONSEQ @ mapmtoi;
    i[MGlobalSeq]      := _Inert_GLOBALSEQ      @ mapmtoi;
    i[MLexicalSeq]     := _Inert_LEXICALSEQ     @ mapmtoi;
    i[MEop]            := _Inert_EOP            @ mapmtoi;
    
    i[MStandaloneExpr] := mapmtoi;
    
    i[MStatSeq]            := _Inert_STATSEQ  @ mapmtoi;
    i[MStandaloneFunction] := _Inert_FUNCTION @ mapmtoi;
    i[MFunction]           := _Inert_FUNCTION @ mapmtoi;
    i[MAssign]             := _Inert_ASSIGN   @ mapmtoi;
    i[MAssignToFunction]   := _Inert_ASSIGN   @ mapmtoi;
    
    
    i[MSingleAssign] := proc(n::m(GeneratedName), e::m)
        singleAssigns[op(n)] := mtoi(e);
        NULL;
    end proc;
    
    i[MSingleUse] := proc(n)
        if assigned(singleAssigns[n]) then
            singleAssigns[n];
        else
            i[MLocal](n);
        end if;
    end proc;
    
    
    i[MIfThenElse] := proc(c, s1, s2)
        if s2 = MStatSeq() then
            _Inert_IF(_Inert_CONDPAIR(mtoi(c), mtoi(s1)));
        else
            _Inert_IF(_Inert_CONDPAIR(mtoi(c), mtoi(s1)), _Inert_STATSEQ(mtoi(s2)))
        end if;
    end proc;
    
    i[MTypedName] := proc(n, t)
        _Inert_DCOLON(_Inert_NAME(n), ToInert(op(t)));
    end proc;
    
end module;
