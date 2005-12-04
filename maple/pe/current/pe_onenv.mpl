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
            
            
            ss := SuperStack(newFrame);
                        
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
            
            
            newFrame := proc()
                Record('vals'=table(), 'dyn'={})
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
                r;
            end proc;
            
            equalsTop := proc(f1)            
                f2 := ss:-top();
                verify(f1:-vals, f2:-vals, 'table') and
                verify(f1:-dyn,  f2:-dyn,  'set');
            end proc;
            
            getVal := proc(key)
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    if member(key, frame:-dyn) then
                        error "can't get dynamic value %1", key;
                    elif assigned(frame:-vals[key]) then
                        return frame:-vals[key];
                    end if; 
                end do;
                error "can't get dynamic value %1", key;
            end proc;
        
            setValDynamic := proc(key)
                frame := ss:-top();
                frame:-vals[key] := evaln(frame:-vals[key]);
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
                frame:-vals[key] := x;
                frame:-dyn := frame:-dyn minus {key};
                NULL;
            end proc;
            
            isStatic := proc(key)
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    if assigned(frame:-vals[key]) then
                        return true;
                    elif member(key, frame:-dyn) then
                        return false;
                    end if;                        
                end do;
                false;
            end proc;
            
            isDynamic := `not` @ isStatic;
            
            display := proc()
                print();
                print("displaying environment");                
                iter := ss:-topDownIterator();
                while iter:-hasNext() do
                    frame := iter:-getNext();
                    print("level");
                    print("vals", op(frame:-vals));
                    print("dyn", frame:-dyn);
                end do;
                print();
            end proc;
        end module;
        
        newEnv:-grow();
        return newEnv;        
    end proc;
    
end module: