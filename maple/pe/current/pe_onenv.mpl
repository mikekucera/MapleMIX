# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export ModuleApply, DYN;

    ModuleApply := proc() local newEnv;
        newEnv := module()
            local 
                ss, mapAddressToTable, prevEnvLink,
                newFrame, doPutVal, rebuildTable, addTable,
                lex, nargsVal;
            export 
                setLink, grow, shrink, shrinkGrow, markTop, equalsTop,
                getVal, putVal, putLoopVarVal, setLoopVar,
                getArgsVal, getArgs, hasArgsVal, putArgsVal,
                setValDynamic, isStatic, isStaticVal, isDynamic, isAssigned,
                isTblValStatic, isTblValAssigned,
                putTblVal, getTblVal, setTblValDynamic, 
                getLex, attachLex, removeLex, hasLex, setNargs, getNargs, hasNargs,
                display, displayNames;
            
##########################################################################################

            ss := SuperStack(newFrame);
            mapAddressToTable := table();  # stores memory addresses of rebuilt tables
            prevEnvLink := 'prevEnvLink';  # reference to previous OnENV in the stack

##########################################################################################

            setLink := proc(x)
                ASSERT( not assigned(prevEnvLink), "prevEnvLink is already assigned" );
                prevEnvLink := x;
                NULL;
            end proc;
            
            newFrame := proc()
                Record('vals'=table(), 'dyn'={}, 'loopvars'={}, 'tbls'=table())
            end proc;

            grow := proc() local frame;
                frame := newFrame();
                if not ss:-empty() then
                    frame:-loopvars := ss:-top():-loopvars;
                end if;
                ss:-push(frame);
                NULL;
            end proc;

            shrink := proc()
                ss:-pop();
                NULL;
            end proc;

            shrinkGrow := proc()
                shrink();
                grow();
            end proc;

            markTop := proc() local r, top;
                ASSERT( not ss:-empty(), "empty stack in environment" );
                r := newFrame();
                top := ss:-top();
                r:-vals := copy(top:-vals);
                r:-dyn  := copy(top:-dyn);
                r:-tbls := copy(top:-tbls);
                r;
            end proc;

            equalsTop := proc(f1) local f2, tableName, r1, r2;
                f2 := ss:-top();
                if not (verify(f1:-vals, f2:-vals, 'table') and
                        verify(f1:-dyn,  f2:-dyn,  'set')) then
                    return false;
                end if;
                for tableName in keys(f1:-tbls) do
                    if not assigned(f2:-tbls[tableName]) then
                        return false;
                    end if;
                    r1 := f1:-tbls[tableName];
                    r2 := f2:-tbls[tableName];
                    if not (verify(r1:-elts, r2:-elts, `table`) and
                            verify(r1:-dyn,  r2:-dyn,  'set') and
                            r1:-link = r2:-link) then
                        return false;
                    end if;
                end do;
                true;
            end proc;

##########################################################################################

            getVal := proc(key::Not(mform), hasDyn) local iter, frame, t, v;
                if nargs > 1 then
                    hasDyn := false;
                end if;
                
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();                    
                    if member(key, frame:-dyn) then
                        error "can't get dynamic value %1", key;
                    elif assigned(frame:-tbls[key]) then
                        if nargs > 1 then
                            t := rebuildTable(frame:-tbls[key], hasDyn);
                            ASSERT( type(t, 'table'), "rebuildTable did not return a table (1)");
                            return t;
                        else
                            t := rebuildTable(frame:-tbls[key]);
                            ASSERT( type(t, 'table'), "rebuildTable did not return a table (2)");
                            return t;
                        end if;
                    elif assigned(frame:-vals[key]) then
                        v := frame:-vals[key];
                        ASSERT( not type(v, 'table'), "found table where it should not be" );
                        return v;
                    end if;
                end do;
                error "can't get dynamic value %1", key;
            end proc;

            
            
            putVal := proc(key::Not(mform), x) local frame;
                # TODO, make type of x MStatic, get rid of SVal calls all over pe_def
                ASSERT( nargs = 2 , "wrong number of args to putVal");
                frame := ss:-top();
                if member(key, frame:-loopvars) then
                    error "variable %1 is a loop variable (assignement to for loop index not allowed)", key;
                end if;
                doPutVal(args);
            end proc;
                        
            
            
            putLoopVarVal := proc(key::Not(mform), x)
                ASSERT( nargs = 2, "wrong number of args to putLoopVarVal" );
                doPutVal(args);
            end proc;
            
                
            
            doPutVal := proc(key, x) local frame, addr, rec;
                frame:=ss:-top();
                frame:-dyn := frame:-dyn minus {key};

                if type(x, 'table') then
                    frame:-vals[key] := evaln(frame:-vals[key]);
                    addr := addressof(eval(x));
                    if assigned(mapAddressToTable[addr]) then
                        ASSERT( type(mapAddressToTable[addr]:-elts, 'table') );
                        frame := ss:-top();
                        frame:-tbls[key] := mapAddressToTable[addr]; # make var point to existing table
                    elif assigned(prevEnvLink) and assigned(prevEnvLink:-mapAddressToTable[addr]) then
                        ASSERT( type(prevEnvLink:-mapAddressToTable[addr]:-elts, 'table') );
                        frame := ss:-top();
                        frame:-tbls[key] := prevEnvLink:-mapAddressToTable[addr];
                    else
                        rec := addTable(key);
                        ASSERT(type(rec:-elts, 'table'));
                        rec:-elts :: 'table' := x;
                    end if;
                else
                    ASSERT( type(x, Not('table')) and type(eval(x), Not('table')), "table where it should not be" );
                    frame:-tbls[key] := evaln(frame:-tbls[key]);
                    frame:-vals[key] := x;
                end if;
                NULL;
            end proc;
            
            
            
            setLoopVar := proc(key::Not(mform)) local frame;
                frame := ss:-top();
                frame:-loopvars := frame:-loopvars union {key};
            end proc;
            
            
            getArgsVal := proc(index::posint)
                getVal(ArgKey(index));
            end proc;
            
            getArgs := proc()
                if not hasNargs() then
                    error "nargs must be static";
                end if;
                seq(getVal(ArgKey(i)), i = 1..nargsVal)
            end proc;
            
            hasArgsVal := proc(index::posint)
                isAssigned(ArgKey(index));
            end proc;
            
            putArgsVal := proc(index::posint, x)
                ASSERT( nargs = 2 );
                putVal(ArgKey(index), x);
            end proc;
            
            
            setValDynamic := proc(key::Not(mform)) local frame;
                frame := ss:-top();
                if member(key, frame:-loopvars) then
                    error "variable %1 is a loop variable (assignement to for loop index not allowed)", key;
                end if;
                #unassign value of key if it is in the env
                frame:-vals[key] := evaln(frame:-vals[key]);
                frame:-tbls[key] := evaln(frame:-tbls[key]);
                
                frame:-dyn := frame:-dyn union {key};
                NULL;
            end proc;  

            
            isStatic := proc(key::Not(mform)) local iter, frame;
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    if member(key, frame:-dyn) then
                        return false;
                    elif assigned(frame:-vals[key]) or assigned(frame:-tbls[key]) then
                        return true;
                    end if;
                end do;
                false;
            end proc;
            
            
            isStaticVal := proc(key::Not(mform)) local iter, frame;
                # does not consider tables
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    if member(key, frame:-dyn) then
                        return false;
                    elif assigned(frame:-vals[key]) then
                        return true;
                    end if;
                end do;
                false;
            end proc;
            
            isDynamic := `not` @ isStatic;
            
            # even though the value if a variable is dynamic we can know
            # statically if it is assigned or not
            isAssigned := proc(key::Not(mform)) local iter, frame;
                iter := ss:-topDownIterator(); 
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    if member(key, frame:-dyn) or
                       assigned(frame:-vals[key]) or 
                       assigned(frame:-tbls[key]) then
                        return true;
                    end if;
                end do;
                false;
            end proc;
            

##########################################################################################

            # precondition, isStatic(table) = true
            rebuildTable := proc(chain::`record`, hasDyn) local tbl, rec, key;
                tbl := table();
                rec := chain;
                do
                    for key in keys(rec:-elts) do
                        if not assigned(tbl[key]) then
                            #tbl[key] := eval(rec:-elts[key]);
                            tbl[key] := rec:-elts[key];
                            if nargs > 1 and tbl[key] = OnENV:-DYN then
                                hasDyn := true;
                            end if;
                        end if;
                    end do;
                    if not assigned(rec:-link) then break end if;
                    rec := rec:-link;
                end do;
                mapAddressToTable[addressof(eval(tbl))] := chain;
                tbl;
            end proc;


            addTable := proc(tblName) local frame, t;
                frame := ss:-top();
                t := Record('link',           # downward link, initially unassigned
                           'elts'=table());   # elements, stores values
                frame:-tbls[tblName] := eval(t,1);
                eval(t,1);
            end proc;


            
            isTblValStatic := proc(tableName::Not(mform), index)
                local foundFrame, rec;
                try
                    foundFrame := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                    rec := foundFrame:-tbls[tableName];
                    do
                        if assigned(rec:-elts[index]) then
                            return not rec:-elts[index] = OnENV:-DYN;
                        elif assigned(rec:-link) then
                            rec := rec:-link;
                        else
                            return false;
                        end if;
                    end do;
                catch "not found" :
                    false;
                end try;
            end proc;
            
            
            isTblValAssigned := proc(tableName::Not(mform), index)
                local foundFrame, rec;
                try
                    foundFrame := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                    rec := foundFrame:-tbls[tableName];
                    do
                        if assigned(rec:-elts[index]) then
                            return true;
                        elif assigned(rec:-link) then
                            rec := rec:-link;
                        else
                            return false;
                        end if;
                    end do;
                catch "not found" :
                    false
                end try;
            end proc;

            
            putTblVal := proc(tableName::Not(mform), index, x)
                local foundFrame, rec;
                ASSERT( nargs = 3, cat("putTblVal expecting 3 args but received ", nargs) );
                if assigned(ss:-top():-tbls[tableName]) then # its at the top
                    rec := ss:-top():-tbls[tableName];
                else
                    try
                        foundFrame := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                        rec := addTable(tableName);
                        rec:-link := foundFrame:-tbls[tableName];
                    catch "not found" :
                        rec := addTable(tableName);
                    end try;
                end if;
                ASSERT( type(rec:-elts, 'table') );
                rec:-elts[index] := x;
                NULL;
            end proc;


            getTblVal := proc(tableName::Not(mform), index)
                local err, frame, rec, val;
                ASSERT( nargs = 2, "getTblVal expected 2 args" );
                err := "table value is dynamic %1[%2]", tableName, index;
                try
                    frame := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                catch:
                    error err;
                end try;

                rec := frame:-tbls[tableName];
                do
                    if not type(rec:-elts, 'table') then
                        print("rec", rec);
                        print("rec:-link", rec:-link);
                        print("rec:-elts", rec:-elts);
                    end if;
                    ASSERT( type(rec:-elts, 'table'), "rec:-elts is not a table!", rec:-elts );
                    if assigned(rec:-elts[index]) then
                        val := rec:-elts[index];
                        if val = OnENV:-DYN then
                            error err;
                        else
                            return val;
                        end if;
                    elif assigned(rec:-link) then
                        rec := rec:-link;
                    else
                        error err;
                    end if;
                end do;
            end proc;


            setTblValDynamic := proc(tableName::Not(mform), index)
                local frame, rec;
                frame := ss:-top();
                if assigned(frame:-tbls[tableName]) then
                    rec := frame:-tbls[tableName];
                else
                    rec := addTable(tableName);
                end if;
                rec:-elts[index] := OnENV:-DYN;
                NULL;
            end proc;




##########################################################################################

            getLex := proc()
                if not assigned(lex) then
                    error "no lexical environment attached";
                end if;
                lex;
            end proc;

            attachLex := proc(x)
                if assigned(lex) then
                    error "this env already has an attached lex: %1", op(lex);
                end if;
                lex := x;
            end proc;

            removeLex := proc()
                lex := 'lex';
            end proc;
            
            hasLex := () -> evalb(assigned(lex));

            setNargs := proc(num)
                nargsVal := num;
            end proc;

            getNargs := () -> nargsVal;
            hasNargs := () -> assigned(nargsVal);

##########################################################################################

            display := proc() local iter, frame, rec, tblName;
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    print("level");
                    print("vals", op(frame:-vals));
                    print("dyn", frame:-dyn);
                    for tblName in keys(frame:-tbls) do
                        rec := frame:-tbls[tblName];
                        print("rec", tblName, eval(rec:-elts,2), `if`(assigned(rec:-link), "linked", "null"));
                    end do;
                end do;
            end proc;
            
            displayNames := proc() local iter, frame, rec, tblName;
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    print("level");
                    print("vals", indices(frame:-vals));
                    print("dyn", frame:-dyn);
                    for tblName in keys(frame:-tbls) do
                        rec := frame:-tbls[tblName];
                        print("rec", tblName, indices(rec:-elts));
                    end do;
                end do;
            end proc;
            
        end module;

        newEnv:-grow();
        return eval(newEnv);
    end proc;

end module:
