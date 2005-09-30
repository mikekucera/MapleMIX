
MNames := module()    
    export

        MProc,
        MParamSeq,
        MLocalSeq,
        MOptionSeq,        

    #expressions

        MExpSeq,
        MInt,
        MString,
        MName,

    #statements

        MStatSeq,
        MIfElse,
        MAssign,
        MAssignToFuncCall;
        
end module;
    
    
M := module()
    export InertToM;
    local mapitm, m;
    
    use MNames in
    
    InertToM := proc(code::inert)
            m[op(0, code)](op(code));           
    end proc;
        
    mapitm := () -> op(map(InertToM, [args]));
    
    m[_Inert_NAME] := MName;
    m[_Inert_INTPOS] := MInt;
    m[_Inert_INTNEG] := MInt @ `-`;
    m[_Inert_STRING] := MString;
    
    m[_Inert_PROC] := MProc @ mapitm;
    m[_Inert_PARAMSEQ] := MParamSeq @ mapitm;
    m[_Inert_LOCALSEQ] := MLocalSeq @ mapitm;
    m[_Inert_OPTIONSEQ] := MOptionSeq @ mapitm;
    m[_Inert_EXPSEQ] := MExpSeq @ mapitm;
    m[_Inert_STATSEQ] := MStatSeq @ mapitm;
    m[_Inert_DESCRIPTIONSEQ] := NULL;
    m[_Inert_GLOBALSEQ] := NULL;
    m[_Inert_LEXICALSEQ] := NULL;
    m[_Inert_EOP] := NULL;
        
    end use;
end module;