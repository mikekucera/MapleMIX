# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export ModuleApply, DYN;

    ModuleApply := proc() local newEnv;
        newEnv := module()
            local 
                ss, mapAddressToTable, prevEnvLink,
                newSetting, doPutVal, rebuildTable, newTableRecord,
                lex, nargsVal, isTblVal, isSetting,
                hasDynamicPart, isAlreadyDynamic,
                putStatic, putDynamic, putTable, putPseudoStatic,
                doMerge, createAssign, addToMask, convertIndex;
            export 
                setLink, grow, pop, equalsTop, merge,
                get, put, setLoopVar,
                getArgsVal, getArgs, hasArgsVal, putArgsVal, setValDynamic, 
                isStatic, isStaticVal, isStaticTable, isDynamic, isAssigned, isGettable,
                isTblValStatic, isTblValAssigned,
                putTblVal, getTblVal, setTblValDynamic, 
                getLex, attachLex, removeLex, hasLex, setNargs, getNargs, hasNargs,
                display, displayNames,
                findSetting, getStaticIndices;
            
##########################################################################################

            ss := SuperStack(newSetting);
            mapAddressToTable := table();  # stores memory addresses of rebuilt tables
            prevEnvLink := 'prevEnvLink';  # reference to previous OnENV in the stack

##########################################################################################

            newSetting := proc()
                Record(
                    'vals' = table(), # Stores bindings for static values.
                    'dyn'  = table(), # Stores bindings for dynamic expressions.
                    'mask' = {},      # Dynamic mask.
                    'tbls' = table(), # Stores partially static table.
                    'loopvars' = {}   # Set of loop variable names, to detect 
                )                     # unsupported assignment to loop variables.
            end proc;
            
            setLink := proc(l)
                ASSERT( not assigned(prevEnvLink), "prevEnvLink is already assigned" );
                prevEnvLink := l;
                NULL;
            end proc;
            
            
            grow := proc() local setting;
                setting := newSetting();
                if not ss:-empty() then
                    setting:-loopvars := ss:-top():-loopvars;
                end if;
                ss:-push(setting);
                NULL;
            end proc;
            
            
            pop := proc()
                return ss:-pop();
            end proc;


            equalsTop := proc(f1) local f2, tableName, r1, r2;
                f2 := ss:-top();
                if not (verify(f1:-vals, f2:-vals, 'table') and
                        verify(f1:-mask, f2:-mask, 'set') and
                        verify(f1:-dyn,  f2:-dyn,  'table')) then
                    return false;
                end if;
                for tableName in keys(f1:-tbls) do
                    if not assigned(f2:-tbls[tableName]) then
                        return false;
                    end if;
                    r1 := f1:-tbls[tableName];
                    r2 := f2:-tbls[tableName];
                    if not (verify(r1:-elts, r2:-elts, 'table') and
                            r1:-link = r2:-link) then
                        return false;
                    end if;
                end do;
                true;
            end proc;
            
            
            # merges environment s1 into the environment on the top of the stack
            # returns 2 statment sequences for residual assignments
            doMerge := proc(s1, s2, mutateNum) local mut, q1, q2, key;
                mut := args[mutateNum];
                q1 := SimpleQueue();
                q2 := SimpleQueue();
                
                for key in keys(s1:-vals) do
                    if assigned(s2:-vals[key]) then
                        if s1:-vals[key] <> s2:-vals[key] then
                            createAssign(q1, s1, key);
                            createAssign(q2, s2, key);
                            addToMask(mut, key);
                        end if;
                    else
                        createAssign(q1, s1, key);
                        addToMask(mut, key);
                    end if;
                end do;
                
                for key in s1:-mask do
                    if not member(key, s2:-mask) then
                        createAssign(q2, s2, key);
                        addToMask(mut, key);
                    end if;
                end do;
                
                q1:-toList(), q2:-toList();
            end proc;
            
            addToMask := proc(setting, key)
                setting:-vals[key] := 'setting:-vals[key]';
                setting:-mask := setting:-mask union {key}
            end proc;
            
            createAssign := proc(q, setting, key)
                if assigned(setting:-vals[key]) then
                    q:-enqueue( MAssign(MLocal(key), MStatic(op(1,setting:-vals[key]))) );
                elif assigned(setting:-dyn[key]) then
                    q:-enqueue( MAssign(MLocak(key), MStatic(setting:-dyn[key])) );
                end if;
            end proc;
            
            merge := proc(s1) local s2, l1, l2, l3, l4;
                s2 := ss:-top();
                l1, l2 := doMerge(s1, s2, 2);
                l3, l4 := doMerge(s2, s1, 1);
                MStatSeq(op(l1), op(l3)), MStatSeq(op(l2), op(l3));
            end proc;
            

##########################################################################################


            get := proc(key::Not(mform), hasDyn) local iter, setting, t, v, tmp;
                if nargs > 1 then
                    hasDyn := false;
                end if;
                
                setting := findSetting(key);
                
                if assigned(setting:-tbls[key]) then
                    if nargs > 1 then
                        rebuildTable(setting:-tbls[key], hasDyn);
                    else
                        rebuildTable(setting:-tbls[key]);
                    end if;
                elif assigned(setting:-vals[key]) then
                    tmp := setting:-vals[key];
                    `if`(type(tmp[1], 'last_name_eval'), 
                        `if`(tmp[1]::builtin, tmp[1], 
                        `if`(tmp[1]::table,eval(tmp[1],2), eval(tmp[1],1))), 
                        tmp[1]);
                elif assigned(setting:-dyn[key]) then
                    setting:-dyn[key];
                else
                    error "can't get dynamic value %1", key
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

            
            getTblVal := proc(tableName::Not(mform), index::MStatic)
                local err, setting, rec, val;
                ASSERT( nargs = 2, "getTblVal expected 2 args" );
                
                err   := "table value is dynamic %1[%2]", tableName, index;
                # throws exeption if not found
                setting := ss:-find( st -> assigned(st:-tbls[tableName]), [err] ); 
                rec   := setting:-tbls[tableName];
                
                do
                    if assigned(rec:-elts[SVal(index)]) then
                        val := rec:-elts[SVal(index)];
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
            

            put := proc(key::Not(mform), x, {loopVarSet := false}) local setting;
                setting := ss:-top();
                if not loopVarSet and member(key, setting:-loopvars) then
                    error "assignement to for loop index variable not supported: %1", key;
                end if;
                
                if type(x, {'table','rtable'}) then
                    putTable(key, x)
                elif x::Dynamic then
                    putDynamic(key, x)
                elif x::PseudoStatic then
                    putPseudoStatic(key, x)
                elif x::Static then
                    putStatic(key, x)
                else 
                    error "Unsupported binding time";
                end if;
                NULL;
            end proc;
            

            putStatic := proc(key, x) local setting;
                setting := ss:-top();
                setting:-tbls[key] := 'setting:-tbls[key]'; #unassign
                setting:-dyn[key]  := 'setting:-dyn[key]';  #unassign
                setting:-mask := setting:-mask minus {key};
                setting:-vals[key] := [x];
            end proc;
            
            putPseudoStatic := proc(key, x) local setting;
                setting := ss:-top();
                setting:-tbls[key] := 'setting:-tbls[key]'; #unassign
                setting:-dyn[key]  := 'setting:-dyn[key]';  #unassign
                setting:-mask := setting:-mask minus {key};
                setting:-vals[key] := [x];
            end proc;
            
            putTable := proc(key, x) local setting, addr, rec;
                setting := ss:-top();
                setting:-vals[key] := 'setting:-vals[key]'; #unassign
                setting:-dyn[key]  := 'setting:-dyn[key]';  #unassign
                setting:-mask := setting:-mask minus {key};
                
                if assigned(setting:-vals[key]) then
                    assign(setting:-vals[key], x);
                else
                    addr := addressof(eval(x));
                    if assigned(mapAddressToTable[addr]) then
                        ASSERT( type(mapAddressToTable[addr]:-elts, 'table') );
                        setting := ss:-top();
                        setting:-tbls[key] := mapAddressToTable[addr]; # make var point to existing table
                    elif assigned(prevEnvLink) and assigned(prevEnvLink:-mapAddressToTable[addr]) then
                        ASSERT( type(prevEnvLink:-mapAddressToTable[addr]:-elts, 'table') );
                        setting := ss:-top();
                        setting:-tbls[key] := prevEnvLink:-mapAddressToTable[addr];
                    else
                        userinfo(7, PE, "Doing as a new table");
                        rec := newTableRecord(key, x);
                        ASSERT(type(rec:-elts, 'table'));
                        # needed, because it is unclear how many levels down
                        # the table is!
                        rec:-elts := x;
                    end if;
                end if;
            end proc;
            
            
            putDynamic := proc(key, x) local setting, r, refreshSubst;
                if not gopts:-getPropagateDynamic() then
                    setValDynamic(key);
                    return;
                end if;
                
                setting := ss:-top();
                setting:-vals[key] := 'setting:-vals[key]'; #unassign
                setting:-tbls[key] := 'setting:-tbls[key]'; #unassign
                setting:-mask := setting:-mask minus {key};
                
                # If the dynamic expression being put back into the environmet
                # has an MSubst then replace it with its corresponding value.
                refreshSubst := proc(n, expr)
                    if member(Header(n), {MLocal, MSingleUse}) then
                        get(op(n));
                    else
                        MSubst(args);
                    end if;
                end proc;
                
                try
                    r := eval(x, MSubst=refreshSubst);   
                    setting:-dyn[key] := substop(r);
                catch :
                    setting:-mask := setting:-mask union {key};
                end try
            end proc;
            
            putTblVal := proc(tableName::Not(mform), index::MStatic, x) 
                local setting, foundsetting, rec, newRec, addr;
                ASSERT( nargs = 3, cat("putTblVal expecting 3 args but received ", nargs) );
                
                userinfo(7, PE, "putting value in table [putTblVal]");
                setting:=ss:-top();
                
                if assigned(setting:-tbls[tableName]) then # its at the top
                    rec := setting:-tbls[tableName];
                else
                    try
                        foundsetting := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                        rec := newTableRecord(tableName, x);
                        rec:-link := foundsetting:-tbls[tableName];
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
                        rec:-elts[SVal(index)] := mapAddressToTable[addr]; # make var point to existing table
                    elif assigned(prevEnvLink) and assigned(prevEnvLink:-mapAddressToTable[addr]) then
                        rec:-elts[SVal(index)] := prevEnvLink:-mapAddressToTable[addr];
                    else
                        newRec := newTableRecord();
                        # don't know how far down the table is, assume that x is the proper name
                        newRec:-elts := x;
                        rec:-elts[SVal(index)] := newRec;
                    end if;
                else    
                    rec:-elts[SVal(index)] := x;
                end if;
                
                setting:-vals[tableName] := 'setting:-vals[tableName]';
                setting:-mask := setting:-mask minus {tableName};
                NULL;
            end proc;
            
            
            
            setLoopVar := proc(key::Not(mform)) local setting;
                setting := ss:-top();
                setting:-loopvars := setting:-loopvars union {key};
            end proc;
            
            
            getArgsVal := proc(index::Or(integer,range)) local x,y;
            	if type(index, 'integer') then
            		get(ArgKey(convertIndex(index)));
            	elif type(index, 'range') then
	            	x := convertIndex(op(1,index));
                	y := convertIndex(op(2,index));
                	op(map(get@ArgKey, [seq(i, i=x..y)]));
	            else
                	error "invalid argument to hasArgsVal: %1", index;
                end if;
            end proc;
            
            getArgs := proc()
                if not hasNargs() then
                    error "nargs must be static";
                end if;
                seq(get(ArgKey(i)), i = 1..nargsVal)
            end proc;
            
            hasArgsVal := proc(index::Or(integer,range)) local x,y;
            	if type(index, 'integer') then
                	isStatic(ArgKey(convertIndex(index)));
                elif type(index, 'range') then
                	x := convertIndex(op(1,index));
                	y := convertIndex(op(2,index));
                	andmap(isStatic@ArgKey, [seq(i, i=x..y)]);
                else
                	error "invalid argument to hasArgsVal: %1", index;
                end if;
            end proc;
            
            # if the index is negative it is converted to positive
            convertIndex := proc(index::integer)::integer;
            	if index >= 0 then
            		index;
            	else 
            		if not hasNargs() then
                   		error "nargs must be static to use negative index";
                	end if; 
                	nargsVal + index + 1;
                end if;
            end proc;
            
            putArgsVal := proc(index::posint, x)
                ASSERT( nargs = 2 );
                put(ArgKey(index), x);
            end proc;
            
            
            setValDynamic := proc(key::Not(mform)) local setting;
                setting := ss:-top();
                if member(key, setting:-loopvars) then
                    error "variable %1 is a loop variable (assignement to for loop index not allowed)", key;
                end if;
                #unassign value of key if it is in the env
                setting:-vals[key] := 'setting:-vals[key]';
                setting:-tbls[key] := 'setting:-tbls[key]';
                setting:-dyn[key]  := 'setting:-dyn[key]';
                setting:-mask := setting:-mask union {key};
                NULL;
            end proc;  

            
            findSetting := proc(key::Not(mform))
                local iter, setting;
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    setting := iter:-getNext();
                    if assigned(setting:-dyn[key]) 
                    or assigned(setting:-tbls[key])
                    or assigned(setting:-vals[key]) then
                        return setting;
                    end if;
                end do;
                error "unassigned value %1", key;
            end proc;
            
            isSetting := proc(key::Not(mform), 
                              itsdynamic::boolean, itsmask::boolean, itsstatic::boolean, notfound::boolean,
                              {considerTables := true}, {considerVals := true})
                local iter, setting;
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    setting := iter:-getNext();
                    if assigned(setting:-dyn[key]) then
                        return itsdynamic;
                    elif member(key, setting:-mask) then
                        return itsmask;
                    elif considerTables and assigned(setting:-tbls[key]) then
                        return itsstatic;
                    elif considerVals and assigned(setting:-vals[key]) then
                        return itsstatic;
                    end if;
                end do;
                return notfound;
            end proc;
            
            
            isStatic := proc(key)
                isSetting(key, false, false, true, false);
            end proc;
            
            isDynamic := `not` @ isStatic;
            
            isStaticVal := proc(key)
                isSetting(key, false, false, true, false, considerTables = false);
            end proc;
            
            isStaticTable := proc(key)
                isSetting(key, false, false, true, false, considerVals = false);
            end proc;
            
            isAssigned := proc(key)
                isSetting(key, true, true, true, false);
            end proc;

            
            isGettable := proc(key) 
                isSetting(key, true, false, true, false);
            end proc;
            
            
##########################################################################################

            # precondition, isStatic(table) = true
            rebuildTable := proc(chain::`record`(elts,link), hasDyn)
			local tbl, rec, tmp, index;

            rec := chain;
			if rec:-elts :: table then
                tbl := table();
                
                do
                    for index in indices(rec:-elts) do
                        if not assigned(tbl[op(index)]) then
                            #ASSERT( not type(rec:-elts[key], 'table'), "found table not being managed by env");
                            
                            if type(rec:-elts[op(index)], 'record(elts,link)') then
                                tbl[op(index)] := rebuildTable(rec:-elts[op(index)]);
                                #tbl[key] := eval(rec:-elts[key],2);
                            else
                                tmp := rec:-elts[op(index)];
                                if eval(tmp,1) = 'rec:-elts'[op(index)] then
                                    if type(eval(tmp,1), 'last_name_eval') then
                                        tbl[op(index)] := eval(tmp,2);
                                        userinfo(8, PE, "eval'd entry", op(index), eval(tmp,2));
                                    else
                                        tbl[op(index)] := tmp;
                                        userinfo(8, PE, "eval'd entry", op(index), tmp);
                                    end if;
                                else
                                    userinfo(8, PE, "normal entry", op(index), tmp);
                                    tbl[op(index)] := tmp;
                                end if;
                            end if;
                            if nargs > 1 and tbl[op(index)] = OnENV:-DYN then
                                hasDyn := true;
                            end if;
                        end if;
                    end do;
                    if not assigned(rec:-link) then break end if;
                    rec := rec:-link;
                end do;
                mapAddressToTable[addressof(eval(tbl))] := chain;
                eval(tbl,1);
            else
                rec:-elts;
            end if;
            end proc;
            
            getStaticIndices := proc(tblName) ::set(list);
            	local foundsetting, rec, dyn, inds, i;
            	try
                    foundsetting := ss:-find( fr -> assigned(fr:-tbls[tblName]) );
                    rec := foundsetting:-tbls[tblName];
                    # TODO, don't use sets, they have bad complexity
                    dyn, inds := {}, {};
                    
                    do
                        for i in indices(rec:-elts) do
                        	if rec:-elts[op(i)] = OnENV:-DYN or i in dyn then
                        		dyn := dyn union {i};
                        	else
                        		inds := inds union {i}
                        	end if;
                        end do;
                        
                        if assigned(rec:-link) then
                            rec := rec:-link;
                        else
                            return inds;
                        end if;
                    end do;
                    
                catch "not found" :
                    {}
                end try;
            end proc;
            
            # Creates a new record to store part of a table.
            # A record will initially be empty.
            #
            newTableRecord := proc(tblName, nam) local setting, rec;
                userinfo(8, PE, "adding new table", `if`(nargs>0, tblName, NULL));
                setting := ss:-top();
                rec := Record(:-link,    # downward link, initially unassigned
                             (:-elts),
                             (:-dynCount) ); # elts, stores values
                rec:-dynCount := 0;
                if nargs > 0 then
                    if nargs=2 and type(nam,'name(table)') then
                        setting:-vals[tblName] := [nam];
                        rec:-elts := nam;
                    else
                        rec:-elts := table();
                        setting:-tbls[tblName] := eval(rec,1);
                    end if;
                else
                    rec:-elts := table();
                end if;
                eval(rec,1);
            end proc;


            isTblVal := proc(tableName::Not(mform), index::MStatic, found::procedure)
                local foundsetting, rec;
                try
                    foundsetting := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                    rec := foundsetting:-tbls[tableName];
                    do
                        if assigned((rec:-elts)[SVal(index)]) then
                            return found(rec:-elts[SVal(index)]);
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
            
            isTblValStatic := proc(tableName::Not(mform), index::MStatic)
                isTblVal(tableName, index, val -> evalb(val <> OnENV:-DYN));
            end proc;
            
            isTblValAssigned := proc(tableName::Not(mform), index::MStatic)
                isTblVal(tableName, index, () -> true);
            end proc;
            
            
            isAlreadyDynamic := proc(rec, index::MStatic) # private
                assigned(rec:-elts[SVal(index)]) and rec:-elts[SVal(index)] = OnENV:-DYN
            end proc;
            
            setTblValDynamic := proc(tableName::Not(mform), index::MStatic)
                local setting, foundsetting, rec;
                setting := ss:-top();
                if assigned(setting:-tbls[tableName]) then # its at the top
                    rec := setting:-tbls[tableName];
                else
                    userinfo(7, PE, "about to create new table [setTblValDynamic]");
                    try # to find another setting with the same name and link it
                        foundsetting := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                        rec := newTableRecord(tableName);
                        rec:-link := foundsetting:-tbls[tableName];
                    catch : # not found so just create a new record
                        rec := newTableRecord(tableName);
                    end try;
                end if;
 
                if not isAlreadyDynamic(rec, index) then
                    rec:-dynCount := rec:-dynCount + 1;
                end if;
                rec:-elts[SVal(index)] := OnENV:-DYN;
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

            display := proc() local printsetting;
                ss:-each( 
                    proc(setting) local rec, tblName;
                        print("level");
                        print("vals", op(setting:-vals));
                        print("dyn", op(setting:-dyn));
                        print("mask", op(setting:-mask));
                        for tblName in keys(setting:-tbls) do
                            rec := setting:-tbls[tblName];
                            print("display: rec", tblName, eval(rec:-elts,2), 
                                  `if`(assigned(rec:-link), "linked", "null"));
                        end do;
                    end proc )
            end proc;
            
            
        end module;

        newEnv:-grow();
        return eval(newEnv);
    end proc;

end module:
