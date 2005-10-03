# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export NewOnENV;
    description "Online knowledge environment";
    
    
    NewOnENV := proc()
        module()
            local valEnv, typeEnv, keyType,
                  getIndices, addProc, getProc;
            export putVal, putType, valIndices, typeIndices, getType,
                   getVal, hasTypeInfo,
                   isStatic, isDynamic,
                   setDynamic, clone, combine, display;
            
            # initialize "instance" variables
            valEnv  := table();
            typeEnv := table();
        
            # normalizes all keys to the same type
            keyType := x -> convert(x, string);
        
            
            # sets a value overwriting previous one
            putVal  := proc(key, val) valEnv[keyType(key)]  := val end proc;
            putType := proc(key, typ) typeEnv[keyType(key)] := typ end proc;
            
            # returns the value
            getVal  := getProc(valEnv);
            getType := getProc(typeEnv);
 
            getProc := proc(tbl)
                proc(key)
                    local n;
                    n := keyType(key);
                    if not assigned(evaln(tbl[n])) then
                        error("no value for " || key);
                    else
                        op(tbl[n]);
                    end if;
                end proc;
            end proc;


            # returns indices
            valIndices  := () -> getIndices(valEnv);
            typeIndices := () -> getIndices(typeEnv);            
            
            getIndices := proc(tbl) local xs;
                xs := indices(tbl);
                `if`(xs = NULL, [], ListTools:-Flatten([xs]))
            end proc;
                    
                    
            # a variable is static if it is mapped to a single value and thats all
            isStatic := key -> assigned(valEnv[keyType(key)]);
            
            # a variable has dynamic properties if it is not fully static
            isDynamic := key -> not isStatic(key);
            
            # returns true if there exists a type environment mapping
            hasTypeInfo := key -> assigned(typeEnv[keyType(key)]);

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
                    newenv:-putVal(i, valEnv[op(i)]);
                end do;
                for i in op(typeIndices()) do
                    newenv:-putType(i, typeEnv[i]);
                end do;

                newenv;
            end proc;
                       
 
            combine := proc(onenv)
                local newenv, i;
                newenv := clone();
                
                for i in op(onenv:-valIndices()) do
                    newenv:-putVal(i, onenv:-getVal(i));
                end do;
                for i in op(onenv:-typeIndices()) do
                    newenv:-putType(i, onenv:-getType(i));
                end do;
                                
                newenv;
            end proc;

            
            display := proc()
                print(op(valEnv), op(typeEnv));
            end proc;
        
        end module;
    end proc;


end module:
