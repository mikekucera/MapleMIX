
FromM := module()
    export ModuleApply;
    local MapStack, lexical,
          inrt, mtoi, mtoi2, mapmtoi, createParamMap, paramMap, singleAssigns,
          createLocalMappingFunctions;


    inrt := table();
    mtoi, mtoi2, mapmtoi := createTableProcs(inrt);


    ModuleApply := proc(code::m)
        singleAssigns := table();
        MapStack := SimpleStack();
        res := mtoi(code);
        singleAssigns := 'singleAssigns';
        MapStack := 'MapStack';
        res;
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
        x -> tbl[x];
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

    
    inrt['string']  := () -> args;
    inrt['Integer'] := () -> args;
    
    inrt[MParam]     := n -> _Inert_PARAM(MapStack:-top()['params'](n));
    inrt[MLocal]     := n -> _Inert_LOCAL(MapStack:-top()['locals'](n));    
    inrt[MGeneratedName]     := inrt[MLocal];
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
    
    inrt[MTableref] := _Inert_TABLEREF @ mapmtoi;
    inrt[MArgs]     := _Inert_ARGS     @ mapmtoi;
    inrt[MNargs]    := _Inert_NARGS    @ mapmtoi;
    
    inrt[MReturn]  := _Inert_RETURN  @ mapmtoi;
    inrt[MError]   := _Inert_ERROR   @ mapmtoi;
    inrt[MUneval]  := _Inert_UNEVAL  @ mapmtoi;
    inrt[MRange]   := _Inert_RANGE   @ mapmtoi;
    inrt[MInequat] := _Inert_INEQUAT @ mapmtoi;
    inrt[MForIn]   := _Inert_FORIN   @ mapmtoi;
    inrt[MForFrom] := _Inert_FORFROM @ mapmtoi;
        
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
    inrt[MStandaloneFunction] := _Inert_FUNCTION @ mapmtoi;
    inrt[MFunction]           := _Inert_FUNCTION @ mapmtoi;
    inrt[MAssign]             := _Inert_ASSIGN   @ mapmtoi;
    inrt[MAssignToFunction]   := _Inert_ASSIGN   @ mapmtoi;
    
    
    inrt[MProc] := proc()
        
        maps := table();
        # function that maps param names to their indicies
        maps['params'] := createParamMap([args][1]);
        # first is a function that keeps track of locals encountered
        # second is a function that generates the new local list
        maps['locals'], newLocalList := createLocalMappingFunctions();
        # the current lexical sequence, which may become smaller
        maps['lexseq'] := CreateLexMap([args][8]);
        # queue that will become the new lexical sequence
        maps['lexqueue'] := SimpleQueue();
        # table mapping a lexical's name to its index in the lexical queue
        maps['lextbl'] := table();
                
        MapStack:-push(maps);
        inertProc := _Inert_PROC(mapmtoi(args));
        MapStack:-pop();
        subsop(2=newLocalList(), inertProc);
    end proc;
    
    
    inrt[MLexicalSeq] := proc()
        lexQueue := MapStack:-top()['lexqueue'];
        _Inert_LEXICALSEQ(op(lexQueue:-toList()));
    end proc;
    
    replaceLexical := proc(f, m, n)
        maps := MapStack:-top();        
        lexTbl := maps['lextbl'];

        if assigned(lexTbl[n]) then
            lexTbl[n];
        else
            if MapStack:-depth() > 1 and f = _Inert_LOCAL then
                temp := MapStack:-pop();
				index := MapStack:-top()['locals'](n);
                MapStack:-push(temp);
                lexpair := _Inert_LEXICALPAIR(_Inert_NAME(n), _Inert_LOCAL(index));
            else
                lexpair := mtoi(maps['lexseq'][n]);
            end if;
            
            lexQueue := maps['lexqueue'];
            lexQueue:-enqueue(lexpair);
            index := lexQueue:-length();
            lexTbl[n] := index;
            index;
        end if;
    end proc;
    
    inrt[MLexicalParam] := proc(n)
        _Inert_LEXICAL_PARAM(replaceLexical(_Inert_PARAM, 'params', n))
    end proc;
    
    inrt[MLexicalLocal] := proc(n)
        _Inert_LEXICAL_LOCAL(replaceLexical(_Inert_LOCAL, 'locals', n))
    end proc;
    
    
    
    inrt[MSingleAssign] := proc(n::m(GeneratedName), e::m)
        singleAssigns[op(n)] := mtoi(e);
        NULL;
    end proc;
    
    
    inrt[MSingleUse] := proc(n)
        if assigned(singleAssigns[n]) then
            singleAssigns[n];
        else
            inrt[MLocal](n);
        end if;
    end proc;
    
    
    inrt[MIfThenElse] := proc(c, s1, s2)
        if s2 = MStatSeq() then
            _Inert_IF(_Inert_CONDPAIR(mtoi(c), mtoi(s1)));
        else
            _Inert_IF(_Inert_CONDPAIR(mtoi(c), mtoi(s1)), _Inert_STATSEQ(mtoi(s2)))
        end if;
    end proc;
    
    inrt[MTypedName] := proc(n, t)
        _Inert_DCOLON(_Inert_NAME(n), ToInert(op(t)));
    end proc;
    
end module;
