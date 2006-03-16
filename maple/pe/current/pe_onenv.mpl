# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export ModuleApply, DYN;

    ModuleApply := proc() local newEnv;
        newEnv := module()
            local 
                ss, mapAddressToTable, prevEnvLink,
                newFrame, doPutVal, rebuildTable, newTableRecord,
                lex, nargsVal, isTblVal, 
                hasDynamicPart, isAlreadyDynamic;
            export 
                setLink, grow, shrink, shrinkGrow, markTop, equalsTop,
                getVal, putVal, bind, putLoopVarVal, setLoopVar,
                getArgsVal, getArgs, hasArgsVal, putArgsVal,
                setValDynamic, isStatic, isStaticVal, isStaticTable, isDynamic, isAssigned,
                isTblValStatic, isTblValAssigned,
                putTblVal, getTblVal, setTblValDynamic, 
                getLex, attachLex, removeLex, hasLex, setNargs, getNargs, hasNargs,
                display, displayNames,
                findFrame;
            
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

            
            
            
            getVal := proc(key::Not(mform), hasDyn) local iter, frame, t, v, tmp;
                if nargs > 1 then
                    hasDyn := false;
                end if;
                
                frame := findFrame(key);
                
                if assigned(frame:-tbls[key]) then
                    if nargs > 1 then
                        rebuildTable(frame:-tbls[key], hasDyn);
                    else
                        rebuildTable(frame:-tbls[key]);
                    end if;
                elif assigned(frame:-vals[key]) then
                    tmp := frame:-vals[key];
                    `if`(type(tmp, 'last_name_eval'), eval(tmp,2), tmp);
                else
                    error "can't get dynamic value %1", key
                end if;
            end proc;
            
            # returns false iff the binding was completely static
            # returns true iff the binding should be residualized
            bind := proc(existingName::Not(mform), {newName::Not(mform):=NULL, argNum::nonnegative:=0, environ:=thismodule})
                local frame, rec, top, val;
                print("bind called");
                frame := environ:-findFrame(existingName, () -> OnENV:-DYN);
                
                if frame = OnENV:-DYN then # nothing was found, completely dynamic
                    setValDynamic(newName);
                    return true;
                end if;
                
                top := ss:-top();
                if assigned(frame:-tbls[existingName]) then
                    rec := frame:-tbls[existingName];
                    if newName <> NULL then
                        top:-tbls[newName] := rec;
                    end if;
                    if argNum > 0 then
                        top:-tbls[ArgKey(argNum)] := rec;
                    end if;
                    hasDynamicPart(rec);
                elif assigned(frame:-vals[existingName]) then
                    val := frame:-vals[existingName];
                    if newName <> NULL then
                        top:-vals[newName] := val;
                    end if;
                    if argNum > 0 then
                        top:-vals[ArgKey(argNum)] := val;
                    end if;
                    false;
                end if;
            end proc;
            
            
            # Returns true iff the table has any index that is dynamic.
            # Used to determine if a table binding should be residualized.
            # Each record masks the one below it.
            # Each record has a dynCounter that counts how many dynamic indexes it has.
            # Unfortunately since records mask ones below them its not enough just to
            # look at the counters, however if a counter is 0 then there is no
            # dynamic index and the record can be skipped.
            # 
            hasDynamicPart := proc(rec) local staticMask, key;
                staticMask := table();
                do
                    if rec:-dynCount > 0 then
                        for key in keys(rec:-elts) do
                            if assigned(staticMask[key]) then
                                next;  
                            elif rec:-elts[key] = OnENV:-DYN then
                                return true; # return as true as soon a dynamic index is found
                            else
                                staticMask[key] := 0; # value doesn't matter
                            end if
                        end do;
                    end if;
                    if not assigned(rec:-link) then 
                        return false; # reached the end of the chain 
                    end if;
                    rec := rec:-link;
                end do;
            end proc;

            
            getTblVal := proc(tableName::Not(mform), index::Not(mform))
                local err, frame, rec, val;
                ASSERT( nargs = 2, "getTblVal expected 2 args" );
                
                err   := "table value is dynamic %1[%2]", tableName, index;
                frame := ss:-find( fr -> assigned((fr:-tbls)[tableName]), [err] ); # throws exeption if not found
                rec   := frame:-tbls[tableName];
                
                do
                    if assigned(rec:-elts[index]) then
                        val := rec:-elts[index];
                        if val = OnENV:-DYN then
                            error err;
                        elif type(val, 'record(link,elts)') then
                            return rebuildTable(val);
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
            
            
            putVal := proc(key::Not(mform), x) local frame;
                userinfo(7, PE, "Putting", x, "at", key, "in env");
                # TODO, make type of x MStatic, get rid of SVal calls all over pe_def
                ASSERT( nargs = 2 , "wrong number of args to putVal");
                frame := ss:-top();
                if member(key, frame:-loopvars) then
                    error "variable %1 is a loop variable (assignement to for loop index not allowed)", key;
                end if;
                doPutVal(key,x);
            end proc;
                        
            
            
            putLoopVarVal := proc(key::Not(mform), x)
                ASSERT( nargs = 2, "wrong number of args to putLoopVarVal" );
                doPutVal(key,x);
            end proc;
            
                
            
            doPutVal := proc(key, x) local frame, addr, rec;
                frame:=ss:-top();
                frame:-dyn := frame:-dyn minus {key};

                if type(x, 'table') then
                    if assigned(frame:-vals[key]) then
                        userinfo(7, PE, "Putting", x, "at", key, "for",frame:-vals[key]);
                        assign(frame:-vals[key], x);
                    else
                        userinfo(7, PE, "Putting", x, "at", key, "as a new entry");
                        # frame:-vals[key] := 'frame:-vals[key]';
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
                            userinfo(7, PE, "Doing as a new table");
                            rec := newTableRecord(key, x);
                            ASSERT(type(rec:-elts, 'table'));
                            # needed, because it is unclear how many levels down
                            # the table is!
                            rec:-elts := x;
                        end if;
                    end if;
                else
                    frame:-tbls[key] := 'frame:-tbls[key]';
                    frame:-vals[key] := x;
                end if;
                NULL;
            end proc;
            
            
            putTblVal := proc(tableName::Not(mform), index::Not(mform), x) local foundFrame, rec, newRec, addr;
                userinfo(7, PE, "Putting table", x, "at", tableName, index, "in env");
                
                ASSERT( nargs = 3, cat("putTblVal expecting 3 args but received ", nargs) );
                if assigned(ss:-top():-tbls[tableName]) then # its at the top
                    rec := ss:-top():-tbls[tableName];
                else
                    try
                        foundFrame := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                        rec := newTableRecord(tableName, x);
                        rec:-link := foundFrame:-tbls[tableName];
                    catch "not found" :
                        rec := newTableRecord(tableName, x);
                    end try;
                end if;
                
                if isAlreadyDynamic(rec, index) then
                    rec:-dynCount := rec:-dynCount - 1;
                end if;
                    
                if type(x, 'table') then
                    addr := addressof(eval(x));
                    if assigned(mapAddressToTable[addr]) then
                        rec:-elts[index] := mapAddressToTable[addr]; # make var point to existing table
                    elif assigned(prevEnvLink) and assigned(prevEnvLink:-mapAddressToTable[addr]) then
                        rec:-elts[index] := prevEnvLink:-mapAddressToTable[addr];
                    else
                        newRec := newTableRecord();
                        # don't know how far down the table is, assume that x is the proper name
                        newRec:-elts := x;
                        rec:-elts[index] := newRec;
                    end if;
                else    
                    rec:-elts[index] := x;
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
                isStatic(ArgKey(index));
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
                frame:-vals[key] := 'frame:-vals[key]';
                frame:-tbls[key] := 'frame:-tbls[key]';
                frame:-dyn := frame:-dyn union {key};
                NULL;
            end proc;  

            
            findFrame := proc(key::Not(mform), 
                              itsdynamic::procedure := (() -> ERROR("dynamic value %1", key)), 
                              itsstatic::procedure := (() -> args), 
                              {considerTables := true},
                              {considerVals := true})
                local iter, frame;
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    if member(key, frame:-dyn) then
                        return itsdynamic()
                    elif considerTables and assigned(frame:-tbls[key]) then
                        return itsstatic(frame)
                    elif considerVals and assigned(frame:-vals[key]) then
                        return itsstatic(frame)
                    end if;
                end do;
                itsdynamic()
            end proc;
            
            
            isStatic := proc(key)
                findFrame(key, () -> false, () -> true);
            end proc;
            
            isDynamic := `not` @ isStatic;
            
            isStaticVal := proc(key)
                findFrame(key, () -> false, () -> true, considerTables = false);
            end proc;
            
            isStaticTable := proc(key)
                findFrame(key, () -> false, () -> true, considerVals = false);
            end proc;
            
            # even though the value if a variable is dynamic we can know
            # statically if it is assigned or not
            isAssigned := proc(key)
                findFrame(key, () -> true, () -> true);
            end proc;
            

##########################################################################################

            # precondition, isStatic(table) = true
            rebuildTable := proc(chain::`record`(elts,link), hasDyn)
                local tbl, rec, tmp, key;
                print("warning, rebuildTable called");
                tbl := table();
                rec := chain;
                
                do
                    for key in keys(rec:-elts) do
                        if not assigned(tbl[key]) then
                            #ASSERT( not type(rec:-elts[key], 'table'), "found table not being managed by env");
                            
                            if type(rec:-elts[key], 'record(elts,link)') then
                                tbl[key] := rebuildTable(rec:-elts[key]);
                                #tbl[key] := eval(rec:-elts[key],2);
                            else
                                tmp := rec:-elts[key];
                                if eval(tmp,1) = 'rec:-elts'[key] then
                                    if type(eval(tmp,1), 'last_name_eval') then
                                        tbl[key] := eval(tmp,2);
                                        userinfo(8, PE, "eval'd entry", key, eval(tmp,2));
                                    else
                                        tbl[key] := tmp;
                                        userinfo(8, PE, "eval'd entry", key, tmp);
                                    end if;
                                else
                                    userinfo(8, PE, "normal entry", key, tmp);
                                    tbl[key] := tmp;
                                end if;
                            end if;
                            if nargs > 1 and tbl[key] = OnENV:-DYN then
                                hasDyn := true;
                            end if;
                        end if;
                    end do;
                    if not assigned(rec:-link) then break end if;
                    rec := rec:-link;
                end do;
                mapAddressToTable[addressof(eval(tbl))] := chain;
                eval(tbl,1);
            end proc;
            
            
            # Creates a new record to store part of a table.
            # A record will initially be empty.
            #
            newTableRecord := proc(tblName, nam) local frame, rec;
                userinfo(8, PE, "adding new table", `if`(nargs>0, tblName, NULL));
                frame := ss:-top();
                rec := Record(:-link,    # downward link, initially unassigned
                             (:-elts),
                             (:-dynCount) ); # elts, stores values
                rec:-dynCount := 0;
                if nargs > 0 then
                    if nargs=2 and type(nam,'name(table)') then
                        frame:-vals[tblName] := nam;
                        rec:-elts := nam;
                    else
                        rec:-elts := table();
                        frame:-tbls[tblName] := eval(rec,1);
                    end if;
                else
                    rec:-elts := table();
                end if;
                eval(rec,1);
            end proc;


            isTblVal := proc(tableName::Not(mform), index::Not(mform), found::procedure)
                local foundFrame, rec;
                try
                    foundFrame := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                    rec := foundFrame:-tbls[tableName];
                    do
                        if assigned((rec:-elts)[index]) then
                            return found(rec:-elts[index]);
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
            
            isTblValStatic := proc(tableName::Not(mform), index::Not(mform))
                isTblVal(tableName, index, val -> evalb(val <> OnENV:-DYN));
            end proc;
            
            isTblValAssigned := proc(tableName::Not(mform), index::Not(mform))
                isTblVal(tableName, index, () -> true);
            end proc;
            
            
            isAlreadyDynamic := proc(rec, index) # private
                assigned(rec:-elts[index]) and rec:-elts[index] = OnENV:-DYN
            end proc;
            
            setTblValDynamic := proc(tableName::Not(mform), index)
                local frame, rec;
                frame := ss:-top();
                if assigned(frame:-tbls[tableName]) then
                    rec := frame:-tbls[tableName];
                else
                    rec := newTableRecord(tableName);
                end if;
                # if its not already dynamic then 
                if not isAlreadyDynamic(rec, index) then
                    rec:-dynCount := rec:-dynCount + 1;
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

            display := proc() local printframe;
                ss:-each( 
                    proc(frame) local rec, tblName;
                        print("level");
                        print("vals", op(frame:-vals));
                        print("dyn", frame:-dyn);
                        for tblName in keys(frame:-tbls) do
                            rec := frame:-tbls[tblName];
                            print("display: rec", tblName, eval(rec:-elts,2), 
                                  `if`(assigned(rec:-link), "linked", "null"));
                        end do;
                    end proc )
            end proc;
            
            # TODO, get rid of this, just delete it
            #displayNames := proc() local iter, frame, rec, tblName;
            #    ss:-each( 
            #        proc(frame) local rec, tblName;
            #            print("level");
            #            print("vals", indices(frame:-vals));
            #            print("dyn", frame:-dyn);
            #            for tblName in keys(frame:-tbls) do
            #                rec := frame:-tbls[tblName];
            #                print("displayNames: rec", tblName, indices(eval(rec:-elts,2)));
            #            end do;
            #        end proc)
            #end proc;
            
        end module;

        newEnv:-grow();
        return eval(newEnv);
    end proc;

end module:
