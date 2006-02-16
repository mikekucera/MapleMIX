# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export NewOnENV, ModuleApply, DYN;
    local newFrame, OldEnv;

    ModuleApply := NewOnENV;

    NewOnENV := proc()
        newEnv := module()
            local ss, newFrame, lex, nargsVal, rebuildTable, prevEnvLink;
            export putVal, getVal, grow, shrink, shrinkGrow, display, markTop,
                   isDynamic, isStatic, isStaticVal, isTblValStatic, isAssigned, 
                   setValDynamic, equalsTop, 
                   mapAddressToTable; #TODO, should not be exported

##########################################################################################

            ss := SuperStack(newFrame);
            mapAddressToTable := table();    # stores memory addresses of rebuilt tables
            prevEnvLink := 'prevEnvLink'; # reference to previous OnENV in the stack

##########################################################################################

            setLink := proc(x)
                prevEnvLink := x;
                NULL;
            end proc;
            
            newFrame := proc()
                Record('vals'=table(), 'dyn'={}, 'readonly'={}, 'tbls'=table())
            end proc;

            grow := proc()
                frame := newFrame();
                if not ss:-empty() then
                    frame:-readonly := ss:-top():-readonly();
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

            markTop := proc()
                r := newFrame();
                top := ss:-top();
                r:-vals := copy(top:-vals);
                r:-dyn := copy(top:-dyn);
                r:-tbls := copy(top:-tbls);
                r;
            end proc;

            equalsTop := proc(f1)
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

            getVal := proc(key::Not(mform), hasDyn)
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
                            return rebuildTable(frame:-tbls[key], hasDyn);
                        else
                            return rebuildTable(frame:-tbls[key]);
                        end if;
                    elif assigned(frame:-vals[key]) then
                        return frame:-vals[key];
                    end if;
                end do;
                error "can't get dynamic value %1", key;
            end proc;

            
            putVal := proc(key::Not(mform), x, readonly)
           
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    if member(key, frame:-dyn) then
                        break
                    elif assigned(frame:-vals[key]) then
                        if frame:-vals[key] = x then
                            return NULL;
                        else
                            break;
                        end if;
                    end if;
                end do;

                frame := ss:-top();
                if nargs <= 2 and member(key, frame:-readonly) then
                    error "variable %1 is read only (assignement to for loop index not allowed)", key;
                end if;
                
                frame:-dyn := frame:-dyn minus {key};

                if type(x, 'table') then
                    frame:-vals[key] := evaln(frame:-vals[key]);
                    addr := addressof(eval(x));
                    
                    if assigned(mapAddressToTable[addr]) then
                        frame := ss:-top();
                        ASSERT( type(mapAddressToTable[addr]:-elts, 'table') );
                        frame:-tbls[key] := mapAddressToTable[addr]; # make var point to existing table
                    elif assigned(prevEnvLink) and assigned(prevEnvLink:-mapAddressToTable[addr]) then
                        frame := ss:-top();
                        ASSERT( type(prevEnvLink:-mapAddressToTable[addr]:-elts, 'table') );
                        frame:-tbls[key] := prevEnvLink:-mapAddressToTable[addr];
                    else
                        rec := addTable(key);
                        #print("rec:-elts :=", key, x);
                        rec:-elts := x;
                        #print("rec:-elts new", rec:-elts);
                    end if;
                else
                    frame:-tbls[key] := evaln(frame:-tbls[key]);
                    frame:-vals[key] := x;
                end if;
                if nargs > 2 then
                    frame:-readonly := frame:-readonly union {key};
                end if;
                NULL;
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
                putVal(ArgKey(index), x);
            end proc;
            
            
            setValDynamic := proc(key::Not(mform))
                frame := ss:-top();
                if member(key, frame:-readonly) then
                    error "variable %1 is read only (assignement to for loop index not allowed)", key;
                end if;
                frame:-vals[key] := evaln(frame:-vals[key]);
                frame:-tbls[key] := evaln(frame:-tbls[key]);
                frame:-dyn := frame:-dyn union {key};
                NULL;
            end proc;  

            
            isStatic := proc(key::Not(mform))
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
            
            
            isStaticVal := proc(key::Not(mform)) # does not consider tables
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
            
            isAssigned := proc(key::Not(mform))
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
            rebuildTable := proc(chain::`record`, hasDyn)
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


            addTable := proc(tblName)
                local t;
                frame := ss:-top();
                t := Record('link',           # downward link, initially unassigned
                           'elts'=table());   # elements, stores values
                frame:-tbls[tblName] := eval(t,1);
                eval(t,1);
            end proc;


            
            isTblValStatic := proc(tableName::Not(mform), index)
                try
                    foundFrame := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                    rec := foundFrame:-tbls[tableName];
                    do
                        if assigned(rec:-elts[index]) then
                            return `if`(rec:-elts[index] = OnENV:-DYN, false, true);
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
                if not type(rec:-elts, 'table') then
                    error "we have a problem"
                end if;
                rec:-elts[index] := x;
                NULL;
            end proc;


            getTblVal := proc(tableName::Not(mform), index)
                err := "table value is dynamic %1[%2]", tableName, index;
                try
                    print("here1");
                    frame := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                    print("here2");
                catch:
                    error err;
                end try;

                print("here3");
                rec := frame:-tbls[tableName];
                print("here4");
                do
                    print("yo1");
                    print(rec);
                    print("yo2");
                    print(index);
                    print("yo3");
                    print(rec:-elts);
                    print("lookup", args);
                    display();
                    if assigned(rec:-elts[index]) then
                        print("here5");
                        val := rec:-elts[index];
                        print("here6");
                        if val = OnENV:-DYN then
                            error err;
                        else
                            return val;
                        end if;
                    elif assigned(rec:-link) then
                        print("here7");
                        rec := rec:-link;
                    else
                        print("here8");
                        error err;
                    end if;
                end do;
            end proc;


            setTblValDynamic := proc(tableName::Not(mform), index)
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

            display := proc()
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
            
            displayNames := proc()
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
        return newEnv;
    end proc;

end module:
