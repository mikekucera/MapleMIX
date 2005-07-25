# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export NewOnENV;
    description "Online knowledge environment";
    
    
    NewOnENV := proc()
        module()
            local params, locals, valEnv, typeEnv, getName,
                  getIndices, addSetProc, addProc;
            export setParams, setLocals, getParam, getLocal,
                   addVal, putVal, addType, putType, addValSet, addTypeSet, getVals, getTypes, valIndices, typeIndices, 
                   getVal,
                   fullyStatic?, fullyDynamic?, dynamic?, has?,
                   setDynamic, clone, combine, display;
            
            # initialize "instance" variables
            valEnv  := table();
            typeEnv := table();
        
            getName := proc(x)
                local head;
                head := op(0, x);
                if head = _Inert_PARAM then
                    convert(getParam(op(1,x)), name);
                elif head = _Inert_LOCAL then
                    convert(getLocal(op(1,x)), name);
                else
                    x;
                end if;
            end proc;
        

            # environment can store mappings for a procedures params and locals
            setParams := proc(ps) params := ps end proc;
            setLocals := proc(ls) locals := ls end proc;
            
            getParam := i -> op(op(i, params));
            getLocal := i -> op(op(i, locals));
            
            
            # sets a value overwriting all previous ones
            putVal  := proc(key, val) valEnv[getName(key)]  := {val} end proc;
            putType := proc(key, typ) typeEnv[getName(key)] := {typ} end proc;
            
            # returns set of values for the given key
            getVals  := key -> valEnv[getName(key)];
            getTypes := key -> typeEnv[getName(key)];
            
            # gets a single value
            getVal := proc(key)
                local n;
                n := getName(key);
                if not assigned(valEnv[n]) then
                    error("no value for " || key);
                elif nops(valEnv[n]) > 1 then
                    error("multiple values for " || key);
                else
                    op(valEnv[n]);
                end if;
            end proc;
 

            # returns indices
            valIndices  := () -> getIndices(valEnv);
            typeIndices := () -> getIndices(typeEnv);            
            
            getIndices := proc(tbl) local xs;
                xs := indices(tbl);
                `if`(xs = NULL, [], xs)
            end proc;
                    
        
            # procedures that add sets of values
            addValSet  := addSetProc(valEnv);            
            addTypeSet := addSetProc(typeEnv);

            addSetProc := proc(tbl)
                proc(key, theSet::set)
                    local n;
                    n := getName(key);
                    if assigned(tbl[n]) then
                        tbl[n] := tbl[n] union theSet;
                    else
                        tbl[n] := theSet;
                    end if;
                end proc;
            end proc;
            
        
            # procedure adds a single value
            addVal  := addProc(valEnv);
            addType := addProc(typeEnv);
            
            addProc := proc(tbl)
                proc(key, x)
                    if assigned(tbl[key]) then
                        tbl[key] := tbl[key] union {x};
                    else
                        tbl[key] := {x};
                    end if;
                end proc;
            end proc;
            
            
            # a variable is static if it is mapped to a single value and thats all
            fullyStatic? := key -> assigned(valEnv[getName(key)]) and nops(valEnv[getName(key)]) = 1 and not assigned(typeEnv[getName(key)]);            
            
            # a variable is completely dynamic if there is absolutley no information available           
            fullyDynamic? := key -> not (assigned(valEnv[getName(key)]) or assigned(typeEnv[getName(key)]));

            # a variable has dynamic properties if it is not fully static
            dynamic? := key -> not fullyStatic?(key);
                
            # returns true iff there exists a mapping for the given key
            has? := key -> not dynamic?(key);
            
            # deletes all information about the given variable
            setDynamic := proc(key)
               local n;
               n := getName(key);
               valEnv[n]  := evaln(valEnv[n]);
               typeEnv[n] := evaln(typeEnv[n]);
            end proc;


            clone := proc()
                local newenv, i;
                newenv := NewOnENV();

                for i in valIndices() do
                    newenv:-addValSet(i, valEnv[i]);
                end do;
                for i in typeIndices() do
                    newenv:-addTypeSet(i, typeEnv[i]);
                end do;

                newenv:-setParams(params);
                newenv:-setLocals(locals);
                newenv;
            end proc;
                       
 
            combine := proc(onenv)
                local newenv, i;
                newenv := clone();
                
                for i in onenv:-valIndices() do
                    newenv:-addValSet(i, onenv:-getVals(i));
                end do;
                for i in onenv:-typeIndices() do
                    newenv:-addTypeSet(i, onenv:-getTypes(i));
                end do;
                                
                newenv;
            end proc;

            
            display := proc()
                print(op(valEnv));
                print(op(typeEnv));
                print(params);
                print(locals);
            end proc;
        
        end module;
    end proc;


end module;