
ToM := module()
    export ModuleApply;    
    local itom, itom2, mapitom,  m, gen;

    m := table();
    itom, itom2, mapitom := createTableProcs(m);

    ModuleApply := proc(obj)::m;
        gen := NameGenerator:-New("m");        
        itom(ToInert(eval(obj)))
    end proc;
 

    # takes an inert expression and splits it
    splitAssigns := proc()
        q := SimpleQueue();          
        processExpr := proc(e::inert)
            # generation of table is a side effect of nested proc
            examineFunc := proc(f)
                local newvar;
                if member(convert(op(1, f), name), intrinsic) then
                    MFunction(mapitom(args));
                else
                    newvar := gen();    
                    q:-enqueue(MAssignToFunction(MSingleUse(newvar), MFunction(mapitom(args))));                
                    MSingleUse(newvar);
                end if; 
            end proc;
            res := eval(e, [_Inert_FUNCTION = examineFunc]);
            itom(res);
        end proc;        
        residualExpressions := map(processExpr, [args]);
        return q:-toList(), residualExpressions;
    end proc;

    
    # splits the given expression, then applies the continuation k to the stripped expression
    split := proc(expr, k)
        assigns, reduced := splitAssigns(expr);
        `if`(nops(assigns) = 0, k(op(reduced)), MStatSeq(op(assigns), k(op(reduced))));
    end proc;    
    
            
    m[MSingleUse] := MSingleUse;
    
    m[_Inert_NAME]     := MName;
    m[_Inert_LOCAL]    := MLocal;
    m[_Inert_PARAM]    := MParam;

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

    m[_Inert_LIST]      := MList     @ mapitom;
    m[_Inert_SET]       := MSet      @ mapitom;

    m[_Inert_EXPSEQ]    := MExpSeq @ mapitom;
    m[_Inert_SUM]       := MSum    @ mapitom;
    m[_Inert_PROD]      := MProd   @ mapitom;

    m[_Inert_RETURN] := MReturn @ mapitom;
    
    m[_Inert_PROC]           := MProc           @ mapitom;
    m[_Inert_PARAMSEQ]       := MParamSeq       @ mapitom;
    m[_Inert_LOCALSEQ]       := MLocalSeq       @ mapitom;
    m[_Inert_OPTIONSEQ]      := MOptionSeq      @ mapitom;    
    m[_Inert_DESCRIPTIONSEQ] := MDescriptionSeq @ mapitom;
    m[_Inert_GLOBALSEQ]      := MGlobalSeq      @ mapitom;
    m[_Inert_LEXICALSEQ]     := MLexicalSeq     @ mapitom;
    m[_Inert_EOP]            := MEop            @ mapitom;        
    

    m[_Inert_STATSEQ] := proc() local standaloneExpr;    
        standaloneExpr := rcurry(split, () -> args);
        MStatSeq( op(map(x -> `if`(IntermediateForms:-isExpr(op(0,x)), standaloneExpr, itom)(x), [args])) );        
    end proc;
    
    m[_Inert_FUNCTION] := () -> split(op(2..-1,[args]), MStandaloneFunction);
    
    m[_Inert_ASSIGN] := (name, expr) -> split(expr, curry(MAssign, itom(name)));

    m[_Inert_IF] := proc()
        if typematch([args], [_Inert_CONDPAIR(c::anything, s::anything)]) then
            split(c, red -> MIfElse(red, itom(s), MStatSeq()));
        elif typematch([args], [_Inert_CONDPAIR(c::anything, s::anything), el::inert(STATSEQ)]) then
            split(c, red -> MIfElse(red, itom(s), itom(el)));
        else
            condpair := op(1, [args]); 
            rest := op(2..-1, [args]);
            c, s := op(1, condpair), op(2, condpair);            
            split(c, red -> MIfElse(red, itom(s), itom(_Inert_IF(rest))));
        end if;
    end proc;

end module:
