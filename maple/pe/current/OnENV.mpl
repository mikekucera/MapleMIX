# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export NewOnENV;
    description "Online knowledge environment";
    
    
    NewOnENV := proc()
        module()
            local valEnv, typeEnv, keyType,
                  getIndices, addSetProc, addProc;
            export addVal, putVal, addType, putType, addValSet, addTypeSet, getVals, getTypes, valIndices, typeIndices, 
                   getVal, hasTypeInfo?,
                   fullyStatic?, fullyDynamic?, dynamic?, has?,
                   setDynamic, clone, combine, display;
            
            # initialize "instance" variables
            valEnv  := table();
            typeEnv := table();
        
            # normalizes all keys to the same type
            keyType := x -> convert(x, string);
        
            
            # sets a value overwriting all previous ones
            putVal  := proc(key, val) valEnv[keyType(key)]  := {val} end proc;
            putType := proc(key, typ) typeEnv[keyType(key)] := {typ} end proc;
            
            # returns set of values for the given key
            getVals  := key -> valEnv[keyType(key)];
            getTypes := key -> typeEnv[keyType(key)];
            
            # gets a single value
            getVal := proc(key)
                local n;
                n := keyType(key);
                if not assigned(evaln(valEnv[n])) then
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
                `if`(xs = NULL, [], ListTools:-Flatten([xs]))
            end proc;
                    
        
            # procedures that add sets of values
            addValSet  := addSetProc(valEnv);            
            addTypeSet := addSetProc(typeEnv);

            addSetProc := proc(tbl)
                proc(key, theSet::set)
                    local n;
                    n := keyType(key);
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
                    local n;
                    n := keyType(key);
                    if assigned(tbl[n]) then
                        tbl[n] := tbl[n] union {x};
                    else
                        tbl[n] := {x};
                    end if;
                end proc;
            end proc;
            
            
            # a variable is static if it is mapped to a single value and thats all
            fullyStatic? := key -> assigned(valEnv[keyType(key)]) and nops(valEnv[keyType(key)]) = 1 and not assigned(typeEnv[keyType(key)]);            
            
            # a variable is completely dynamic if there is absolutley no information available           
            fullyDynamic? := key -> not (assigned(valEnv[keyType(key)]) or assigned(typeEnv[keyType(key)]));

            # a variable has dynamic properties if it is not fully static
            dynamic? := key -> not fullyStatic?(key);
                
            # returns true iff there exists a mapping for the given key
            has? := key -> not dynamic?(key);
            
            # returns true if there exists a type environment mapping
            hasTypeInfo? := key -> assigned(typeEnv[keyType(key)]);

            # deletes all information about the given variable
            setDynamic := proc(key)
               local n;
               n := keyType(key);
               valEnv[n]  := evaln(valEnv[n]);
               typeEnv[n] := evaln(typeEnv[n]);
            end proc;


            clone := proc()
                local newenv, i;
                newenv := NewOnENV();

                for i in op(valIndices()) do
                    newenv:-addValSet(i, valEnv[op(i)]);
                end do;
                for i in op(typeIndices()) do
                    newenv:-addTypeSet(i, typeEnv[i]);
                end do;

                newenv;
            end proc;
                       
 
            combine := proc(onenv)
                local newenv, i;
                newenv := clone();
                
                for i in op(onenv:-valIndices()) do
                    newenv:-addValSet(i, onenv:-getVals(i));
                end do;
                for i in op(onenv:-typeIndices()) do
                    newenv:-addTypeSet(i, onenv:-getTypes(i));
                end do;
                                
                newenv;
            end proc;

            
            display := proc()
                print(op(valEnv), op(typeEnv));
            end proc;
        
        end module;
    end proc;


end module;
