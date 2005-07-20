# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export NewOnENV;
    description "Online knowledge environment";
    
    
    NewOnENV := proc()
        module()
            local params, locals, valEnv, typeEnv,
                  getIndices, addSetProc, addProc;
            export setParams, setLocals, getParam, getLocal,
                   addVal, putVal, addType, putType, addValSet, addTypeSet, getVals, getTypes, valIndices, typeIndices,
                   static?, dynamic?, both?, has?,
                   setDynamic, combine;
            
            # initialize "instance" variables
            valEnv  := table();
            typeEnv := table();
        
        
            # environment can store mappings for a procedures params and locals
            setParams := proc(ps) params := ps end proc;
            setLocals := proc(ls) locals := ls end proc;
            
            getParam := i -> op(i, params);
            getLocal := i -> op(i, locals);
            
            
            # sets a value overwriting all previous ones
            putVal  := proc(key, val) valEnv[key]  := {val} end proc;
            putType := proc(key, typ) typeEnv[key] := {typ} end proc;
            
            # returns set of values for the given key
            getVals  := key -> valEnv[key];
            getTypes := key -> typeEnv[key];
            
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
                    if assigned(tbl[key]) then
                        tbl[key] := tbl[key] union theSet;
                    else
                        tbl[key] := theSet;
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
            static? := key -> assigned(valEnv[key]) and nops(valEnv[key]) = 1 and not assigned(typeEnv[key]);            
            
            # a variable is completely dynamic if there is absolutley no information available           
            dynamic? := key -> not (assigned(valEnv[key]) or assigned(typeEnv[key]));                
                
            # does a variable have both static and dynamic properties?
            both? := key -> not (static?(key) or dynamic?(key));
            
            # returns true iff there exists a mapping for the given key
            has? := key -> not dynamic?(key);
            
            # deletes all information about the given variable
            setDynamic := proc(key)
               valEnv[key]  := evaln(valEnv[key]);
               typeEnv[key] := evaln(typeEnv[key]);
            end proc;

                        
            combine := proc(onenv)
                local newenv, i;
                newenv := NewOnENV();
                
                for i in valIndices() do
                    newenv:-addValSet(i, valEnv[i]);
                end do;
                for i in typeIndices() do
                    newenv:-addTypeSet(i, typeEnv[i]);
                end do;
                
                for i in onenv:-valIndices() do
                    newenv:-addValSet(i, onenv:-getVals(i));
                end do;
                for i in onenv:-typeIndices() do
                    newenv:-addTypeSet(i, onenv:-getTypes(i));
                end do;
                
                newenv:-setParams(params);
                newenv:-setLocals(locals);
                
                newenv;
            end proc;
            
        
        end module;
    end proc;


end module;