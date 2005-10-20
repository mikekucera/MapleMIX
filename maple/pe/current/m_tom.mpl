
ToM := module()
    export ModuleApply;    
    local MapStack,
    	  itom, itom2, mapitom,  m, gen, createMap, getVar;

    m := table();
    itom, itom2, mapitom := createTableProcs(m);
    
    # TODO, replace New in NameGenerator with ModuleApply
    gen := NameGenerator("m");
    
    
    ModuleApply := proc(x::inert)::m;        	    	
    	MapStack := SimpleStack();
    	res := itom(x);
		MapStack := 'MapStack';
		res;
    end proc;        

    # maps param and local indices to their names
    createMap := proc(varSeq)
        tbl := table();
        index := 0;
        for n in varSeq do     
            index := index + 1;
            tbl[index] := op(`if`(op(0,n)=_Inert_DCOLON, [1,1], 1), n);
        end do; 
        tbl;
    end proc;
    
    createLexMap := proc(lexicalseq)
        tbl := table();
        i := 1;
        for lexpair in lexicalseq do
            tbl[i] := op([2,1],lexpair);
            i := i + 1;
        end do;
        tbl;
    end proc;

    getVar := proc(mapname, x)
        maps := MapStack:-top();
        tbl := maps[mapname];
    	if assigned(tbl[x]) then
    		tbl[x];
    	else
    		error cat("(in ToM), No var found for name: ", x)
    	end if;
    end proc;
    
    getLexVar := proc(mapname, x)        
        maps := MapStack:-pop();
        lexIndex := maps['lex'][x];
        res := getVar(mapname, lexIndex);
        MapStack:-push(maps);
        res;
    end proc;

    
    # takes an inert expression and splits it
    splitAssigns := proc(e::inert)
        q := SimpleQueue();          

        # generation of table is a side effect of nested proc
        examineFunc := proc(f)
            local newvar;
            if member(convert(op(1, f), name), intrinsic) then
                MFunction(mapitom(args));
            else
                newvar := gen();    
                q:-enqueue(MAssignToFunction(MGeneratedName(newvar), MFunction(mapitom(args))));                
                MSingleUse(newvar);
            end if; 
        end proc;
        
        res := eval(e, [_Inert_FUNCTION = examineFunc]);
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
    
    # TODO, why do I have to do this?
    m[MSingleUse] := MSingleUse;
    m[MFunction] := MFunction;
    
    m[_Inert_NAME]     := MName;
    m[_Inert_LOCAL]    := x -> MLocal(getVar('locals', x));
    m[_Inert_PARAM]    := x -> MParam(getVar('params', x));
    
    m[_Inert_LEXICAL_LOCAL] := x -> MLexicalLocal(getLexVar('locals', x));
    m[_Inert_LEXICAL_PARAM] := x -> MLexicalParam(getLexVar('params', x));
    m[_Inert_LEXICALPAIR]  := MLexicalPair @ itom2;
        
    m[_Inert_ASSIGNEDNAME] := MAssignedName;

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
    
    m[_Inert_PARAMSEQ]       := MParamSeq       @ mapitom;
    m[_Inert_LOCALSEQ]       := MLocalSeq       @ mapitom;
    m[_Inert_OPTIONSEQ]      := MOptionSeq      @ mapitom;    
    m[_Inert_DESCRIPTIONSEQ] := MDescriptionSeq @ mapitom;
    m[_Inert_GLOBALSEQ]      := MGlobalSeq      @ mapitom;    
    m[_Inert_EOP]            := MEop            @ mapitom;
                                            
    m[_Inert_PROC] := proc()
        maps := table();
        maps['params'] := createMap([args][1]);
        maps['locals'] := createMap([args][2]);
        maps['lex']    := createLexMap([args][8]);
        MapStack:-push(maps);
        MProc(mapitom(args));
    end proc;
    
    # The lexical sequence comes after the proc body so its ok to pop the stacks 
    # here. Actually its needed because the locals and params in the lexical 
    # pairs refer to the outer environment.
    m[_Inert_LEXICALSEQ] := proc()
         MapStack:-pop();
         MLexicalSeq(mapitom(args));
    end proc;

    m[_Inert_STATSEQ] := proc() local standaloneExpr;    
        standaloneExpr := rcurry(split, MStandaloneExpr);
        f := x -> ssop(`if`(IntermediateForms:-isExpr(op(0,x)), standaloneExpr, itom)(x));
        #TODO: if result is a single statment then don't wrap it in a statseq
        MStatSeq(op(map(f, [args])));        
    end proc;
    
    m[_Inert_FUNCTION] := () ->split([args][2], curry(MStandaloneFunction, itom([args][1])));
    
    m[_Inert_ASSIGN] := (name, expr) -> split(expr, curry(MAssign, itom(name)));
    
    m[_Inert_RETURN] := e -> split(e, MReturn);

    m[_Inert_IF] := proc()
        if typematch([args], [_Inert_CONDPAIR('c'::anything, 's'::anything)]) then
            split(c, red -> MIfThenElse(red, itom(s), MStatSeq(MStandaloneExpr(MExpSeq()))));
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
