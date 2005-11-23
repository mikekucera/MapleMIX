# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export NewOnENV, ModuleApply;
    description "Online knowledge environment";

    ModuleApply := NewOnENV;

    NewOnENV := proc()
        module()
            local valEnv, typeEnv, keyType,
                  getIndices, addProc, getProc, lex,
                  argsVal, nargsVal;
            export putVal, putType, valIndices, typeIndices, getType,
                   setArgs, getArgs, setNargs, getNargs, hasNargs,
                   attachLex, removeLex, getLex, hasLex,
                   getVal, hasTypeInfo,
                   isStatic, isDynamic,
                   setDynamic, clone, combine, overwrite, display;

            # initialize "instance" variables
            valEnv  := table();
            typeEnv := table();


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

            setArgs := proc(tbl)
                argsVal := tbl;
            end proc;

            setNargs := proc(num)
                nargsVal := num;
            end proc;

            getArgs  := () -> argsVal;
            getNargs := () -> nargsVal;

            hasNargs := () -> assigned(nargsVal);



            # normalizes all keys to the same type
            keyType := x -> convert(x, string);


            # sets a value overwriting previous one
            putVal  := proc(key, val) valEnv[keyType(key)]  := val end proc;
            putType := proc(key, typ) typeEnv[keyType(key)] := typ end proc;

            # returns the value
            getVal  := getProc(valEnv);
            getType := getProc(typeEnv);

            getProc := proc(tbl)
                proc(key) local n;
                    n := keyType(key);
                    if assigned(tbl[n]) then
                        tbl[n];
                    else
                        error "no value for %1", key;
                    end if;
                end proc;
            end proc;


            # returns indices
            valIndices  := () -> keys(valEnv);
            typeIndices := () -> keys(typeEnv);


            # a variable is static if it is mapped
            isStatic := key -> assigned(valEnv[keyType(key)]);


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

            overwrite := proc(onenv)
                valEnv  := table();
                typeEnv := table();
                for i in op(onenv:-valIndices()) do
                    putVal(i, onenv:-getVal(i));
                end do;
                for i in op(onenv:-typeIndices()) do
                    putType(i, onenv:-getType(i));
                end do;
                NULL;
            end proc;

            display := proc()
                print(op(valEnv), op(typeEnv));
            end proc;

        end module;
    end proc;


end module:
