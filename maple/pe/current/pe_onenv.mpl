# Online "knowledge" environment
# Stores a set of values for each variable and also possibly a set of types


OnENV := module()
    export NewOnENV, ModuleApply;
    local newFrame, OldEnv;

    ModuleApply := NewOnENV;

    NewOnENV := proc()
        newEnv := module()
            local ss, newFrame, lex, argsVal, nargsVal;
            export putVal, getVal, grow, shrink, shrinkGrow, display, markTop,
                   isDynamic, isStatic, setValDynamic, equalsTop;

##########################################################################################

            ss := SuperStack(newFrame);

##########################################################################################

            newFrame := proc()
                Record('vals'=table(), 'dyn'={}, 'tbls'=table())
            end proc;

            grow := proc()
                ss:-push(newFrame());
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

            getVal := proc(key)
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    if member(key, frame:-dyn) then
                        error "can't get dynamic value %1", key;
                    elif assigned(frame:-vals[key]) then
                        return frame:-vals[key];
                    elif assigned(frame:-tbls[key]) then
                        error "reconstitution of table value not implemented yet"
                    end if;
                end do;
                error "can't get dynamic value %1", key;
            end proc;

            setValDynamic := proc(key)
                frame := ss:-top();
                frame:-vals[key] := evaln(frame:-vals[key]);
                frame:-tbls[key] := evaln(frame:-tbls[key]);
                frame:-dyn := frame:-dyn union {key};
                NULL;
            end proc;


            putVal := proc(key, x)
                #frame := ss:-top();
                #frame:-vals[key] := x;
                #frame:-dyn := frame:-dyn minus {key};
                #NULL;
                # TODO, code above is more general and efficient
                # code below can lead to better specialization but has more overhead

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
                frame:-dyn := frame:-dyn minus {key};

                if type(x, `table`) then
                    frame:-vals[key] := evaln(frame:-vals[key]);
                    rec := addTable(key);
                    rec:-elts := copy(x);
                else
                    frame:-tbls[key] := evaln(frame:-tbls[key]);
                    frame:-vals[key] := x;
                end if;
                NULL;
            end proc;

            isStatic := proc(key)
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

            isDynamic := `not` @ isStatic;

##########################################################################################


            addTable := proc(tblName)
                frame := ss:-top();
                frame:-tbls[tblName] := Record('link', # downward link, initially unassigned
                                               'elts'=table(), # elements, stores values
                                               'dyn'={}); # dynamic mask
            end proc;


            putTblVal := proc(tableName, index, x)
                if assigned(ss:-top():-tbls[tableName]) then # its at the top
                    rec := ss:-top():-tbls[tableName];
                    rec:-elts[index] := x;
                    rec:-dyn := rec:-dyn minus {index};
                else
                    try
                        foundRec := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                        rec := addTable(tableName);
                        rec:-elts[index] := x;
                        rec:-link := foundRec:-tbls[tableName];
                    catch "not found" :
                        rec := addTable(tableName);
                        rec:-elts[index] := x;
                    end try;
                end if;
                NULL;
            end proc;


            getTblVal := proc(tableName, index)
                err := "table value is dynamic %1[%2]", tableName, index;
                try
                    frame := ss:-find( fr -> assigned(fr:-tbls[tableName]) );
                catch:
                    error err;
                end try;

                rec := frame:-tbls[tableName];
                do
                    if member(index, rec:-dyn) then
                        error err;
                    elif assigned(rec:-elts[index]) then
                        return rec:-elts[index];
                    elif assigned(rec:-link) then
                        print("link", rec:-link);
                        rec := rec:-link;
                    else
                        error err;
                    end if;
                end do;
            end proc;


            setTblValDynamic := proc(tableName, index)
                frame := ss:-top();
                if assigned(frame:-tbls[tableName]) then
                    rec := frame:-tbls[tableName];
                    rec:-vals[index] := evaln(rec:-vals[index]);
                    rec:-dyn := rec:-dyn union {index};
                else
                    rec:-addTable(tableName);
                    rec:-dyn := {index};
                end if;
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

            setArgs := proc(tbl)
                argsVal := tbl;
            end proc;

            setNargs := proc(num)
                nargsVal := num;
            end proc;

            getArgs  := () -> argsVal;
            getNargs := () -> nargsVal;

            hasNargs := () -> assigned(nargsVal);

##########################################################################################

            display := proc()
                print();
                print("displaying environment");
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    print("level");
                    print("vals", op(frame:-vals));
                    print("dyn", frame:-dyn);
                    for tblName in keys(frame:-tbls) do
                        rec := frame:-tbls[tblName];
                        print("rec", tblName, op(rec:-elts), rec:-dyn, `if`(rec:-link=NULL, "linked", "null"));
                    end do;
                end do;
                print();
            end proc;
        end module;

        newEnv:-grow();
        return newEnv;
    end proc;

end module:
