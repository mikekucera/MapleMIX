
FromM := module()
    export ModuleApply;
    local i, mtoi, mtoi2, mapmtoi, createParamMap, paramMap;

    i := table();
    mtoi, mtoi2, mapmtoi := createTableProcs(i);

    ModuleApply := proc(code::m(Proc))
        paramMap := createParamMap(Params(code));
        mtoi(code);        
    end proc;
    
    
    # returns a table that maps param names to their indices
    createParamMap := proc(params)
        local tbl, param, index;
        tbl := table();
        index := 1;
        for param in params do
            tbl[op(param)] := index;
            index := index + 1;
        end do;
        tbl;
    end proc;

    
    i[MName]  := _Inert_NAME;
    i[MLocal] := _Inert_LOCAL;
    i[MParam] := n -> _Inert_PARAM(paramMap[n]);

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
    
    
    
    i[MStatSeq]            := _Inert_STATSEQ  @ mapmtoi;
    i[MStandaloneFunction] := _Inert_FUNCTION @ mapmtoi;
    i[MFunction]           := _Inert_FUNCTION @ mapmtoi;
    i[MAssign]             := _Inert_ASSIGN   @ mapmtoi;
    i[MAssignToFunction]   := _Inert_ASSIGN   @ mapmtoi;
    i[MSingleUse]          := _Inert_LOCAL;
    
    i[MIfElse] := proc(c, s1, s2)
        _Inert_IF(_Inert_CONDPAIR(mtoi(c), mtoi(s1)), _Inert_STATSEQ(mtoi(s2)))
    end proc;
    
end module;
