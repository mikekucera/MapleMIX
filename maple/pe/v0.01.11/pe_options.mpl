
PEOptions := module()
    #local ;
    option package;
    export ModuleApply,
           PURE, INTRINSIC, DYNAMIC, UNKNOWN;
           # PURE: if all args static then call, otherwise specialize
           # INTRINSIC: if all args static then call, otherwise residualize
           # DYNAMIC: always residualize
           # UNKNOWN: always specialize


    ModuleApply := proc()
        module()
            export
                addFunction,
                setConsiderExpseq,   getConsiderExpseq,
                setIgnoreCommands,   getIgnoreCommands,
                setShareFunctions,   getShareFunctions,
                setPropagateDynamic, getPropagateDynamic,
                setInlineAssigns, getInlineAssigns;
            local
                level, setLevel, getLevel, mutex,
                considerExpseq, ignoreCommands, inlineAssigns,
                functions, funcOpt, hasFuncOpt;

            level := infinity;
            setLevel := proc(n::Or(posint,infinity))
                level := n;
                NULL;
            end proc;
            getLevel := () -> level;

            considerExpseq := true;
            setConsiderExpseq := proc(x::boolean)
                considerExpseq := x;
                NULL;
            end proc;
            getConsiderExpseq := () -> considerExpseq;


            ignoreCommands := false;
            setIgnoreCommands := proc(x::boolean)
                ignoreCommands := x;
                NULL;
            end proc;
            getIgnoreCommands := () -> ignoreCommands;

            mutex := true; # true will enable function sharing but disable dynamic propagation
            setShareFunctions := proc(x::boolean := true)
                mutex := x;
                NULL;
            end proc;
            getShareFunctions := () -> mutex;
            setPropagateDynamic := proc(x::boolean := true)
                mutex := not x;
                NULL:
            end proc;
            getPropagateDynamic := () -> not mutex;
            

            inlineAssigns := false;
            setInlineAssigns := proc(x::boolean := true)
                inlineAssigns := x;
                NULL:
            end proc;
            getInlineAssigns := () -> inlineAssigns;
            
            
            functions := table();

            addFunction := proc(typ :: {identical(PEOptions:-PURE),
                                        identical(PEOptions:-INTRINSIC),
                                        identical(PEOptions:-DYNAMIC)},
                                f   :: `procedure`)
                functions[eval(f)] := typ;
            end proc;

            funcOpt := proc(f)
                `if`(hasFuncOpt(f), functions[eval(f)], UNKNOWN);
            end proc;

            hasFuncOpt := proc(f)
                evalb(assigned(functions[eval(f)]));
            end proc;

        end module;
    end proc;

end module:
