
ToM := module()
    export ModuleApply;    
    local procToM, toM,
    	  itom, itom2, mapitom,  m, gen, createMap, paramMap, localMap, getVar;

    m := table();
    itom, itom2, mapitom := createTableProcs(m);
    gen := NameGenerator:-New("m");

    
    ModuleApply := proc(x)::m;
    	`if`(type(x, procedure), procToM(x), toM(x))
    end proc;
    
    # Converts a procedure to M
    procToM := proc(p::procedure)::m;
    	local inert;        
        inert := ToInert(eval(p));        
        paramMap := (createMap @ Params)(inert);
        localMap := (createMap @ Locals)(inert);
        itom(inert);
    end proc;
 
    # converts any value to M
 	toM := proc(x)::m;
 		itom(ToInert(x));
 	end proc;
    
    # mapes param and local indices to their names
    createMap := proc(varSeq)
        tbl := table();
        index := 0;
        for n in varSeq do     
            index := index + 1;
            tbl[index] := op(`if`(op(0,n)=_Inert_DCOLON, [1,1], 1), n);
        end do;    
        tbl;
    end proc;
    
    getVar := proc(tbl, x)
    	if assigned(tbl[x]) then
    		tbl[x];
    	else
    		error cat("No var fould for name: ", x)
    	end if;
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

    
    # splits the given expression, th    en applies the continuation k to the stripped expression
    split := proc(expr, k)
        assigns, reduced := splitAssigns(expr);
        if nops(assigns) = 0 then
        	k(op(reduced));
        else
        	MStatSeq(op(assigns), k(op(reduced)));
        end if;
    end proc;    
    
            
    m[MSingleUse] := MSingleUse;
    
    m[_Inert_NAME]     := MName;
    m[_Inert_LOCAL]    := i -> MLocal(getVar(localMap, i));
    m[_Inert_PARAM]    := i -> MParam(getVar(paramMap, i));

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
        standaloneExpr := rcurry(split, MStandaloneExpr);
        f := x -> ssop(`if`(IntermediateForms:-isExpr(op(0,x)), standaloneExpr, itom)(x));
        #TODO: if result is a single statment then don't wrap it in a statseq
        MStatSeq(op(map(f, [args])));        
    end proc;
    
    m[_Inert_FUNCTION] := () -> split(op(2..-1,[args]), MStandaloneFunction);
    
    m[_Inert_ASSIGN] := (name, expr) -> split(expr, curry(MAssign, itom(name)));

    m[_Inert_IF] := proc()
        if typematch([args], [_Inert_CONDPAIR('c'::anything, 's'::anything)]) then
            split(c, red -> MIfThenElse(red, itom(s), MStatSeq()));
        elif typematch([args], [_Inert_CONDPAIR('c'::anything, 's'::anything), 'el'::inert(STATSEQ)]) then
            split(c, red -> MIfThenElse(red, itom(s), itom(el)));
        else
            condpair := op(1, [args]); 
            rest := op(2..-1, [args]);
            c, s := op(1, condpair), op(2, condpair);            
            split(c, red -> MIfThenElse(red, itom(s), itom(_Inert_IF(rest))));
        end if;
    end proc;
    
    # converts a type assertion into a 'typed name'
    m[_Inert_DCOLON] := proc(n, t)
        MTypedName(op(n), MType(FromInert(t)));
    end proc;

end module:
