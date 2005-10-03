
    
M := module()
    export ModuleApply, Print;
    local mapitm, m, gen, intrinsic;
    
    # set of builtin function names
    intrinsic := {anames(builtin)};
    
    
    # just calls itom
    ModuleApply := proc(code::inert)::m;
        gen := makeNameGenerator("m");
        itom(code)
    end proc;
    
        

    
    # used to print out M forms in a readable way
    Print := proc(m::m)
        printspaces := proc(num)
            from 1 to num*2 do
                printf(" ");
            end do;
        end proc;        
        doPrint := proc(indent, f)            
            if type(f, function) then
                printspaces(indent);
                printf("%a\n", op(0,f));              
                op(map(curry(procname, indent+1), [op(f)]));
            else
                printspaces(indent);
                printf("%a\n", f);
            end if;
        end proc;        
        doPrint(0, m);        
    end proc;
    
    
    
    
    itom := code -> m[op(0, code)](op(code));                       
    mapitom := () -> op(map(itom, [args]));
    
    
    # takes an inert expression and splits it
    split := proc()
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
    
    
    m[_Inert_STATSEQ] := proc() local standaloneExpr;    
        standaloneExpr := proc(expr::inert)
            assigns, reduced := split(expr);
            MStatSeq(op(assigns), op(reduced));
        end proc;
        MStatSeq( op(map(x -> `if`(member(op(0,x), expressionForms), standaloneExpr, itom)(x), [args])) );
    end proc;
    
        
    m[MSingleUse] := MSingleUse;
    
    m[_Inert_NAME] := MName;
    m[_Inert_LOCAL] := MLocal;
    m[_Inert_PARAM] := MParam;
    m[_Inert_INTPOS] := MInt;
    m[_Inert_INTNEG] := MInt @ `-`;
    m[_Inert_STRING] := MString;
    
    m[_Inert_PROC] := MProc @ mapitom;
    m[_Inert_PARAMSEQ] := MParamSeq @ mapitom;
    m[_Inert_LOCALSEQ] := MLocalSeq @ mapitom;
    m[_Inert_OPTIONSEQ] := MOptionSeq @ mapitom;
    m[_Inert_EXPSEQ] := MExpSeq @ mapitom;
    m[_Inert_SUM] := MSum @ mapitom;
    m[_Inert_PROD] := MProd @ mapitom;
    
    m[_Inert_DESCRIPTIONSEQ] := NULL;
    m[_Inert_GLOBALSEQ] := NULL;
    m[_Inert_LEXICALSEQ] := NULL;
    m[_Inert_EOP] := NULL;        
    
    m[_Inert_FUNCTION] := proc()
        assigns, reduced := split(op(2..-1, [args]));
        MStatSeq(op(assigns), MStandaloneFunction(op(reduced)));
    end proc;
    
    m[_Inert_ASSIGN] := proc(name, expr)
        assigns, reduced := split(expr);
        MStatSeq(op(assigns), MAssign(itom(name), op(reduced)))
    end proc;
    

end module;