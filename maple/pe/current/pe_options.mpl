
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
                addFunction;
            local 
                level, setLevel, getLevel,
                considerExpseq, setConsiderExpseq, getConsiderExpseq,
                ignoreCommands, setIgnoreCommands, getIgnoreCommands,
                functions, funcOpt, hasFuncOpt;
            
            # mutator functions return thismodule so that they may be chained
            level := infinity;
            setLevel := proc(n::Or(posint,infinity))
                level := n;
                thismodule;
            end proc;
            getLevel := () -> level;
            
            considerExpseq := true;
            setConsiderExpseq := proc(x::boolean)
                considerExpseq := x;
                thismodule;
            end proc;
            getConsiderExpseq := () -> considerExpseq;
            
            
            ignoreCommands := false;
            setIgnoreCommands := proc(x::boolean)
                ignoreCommands := x;
                thismodule;
            end proc;
            getIgnoreCommands := () -> ignoreCommands;
            
            
            functions := table();
            
            addFunction := proc(typ :: {identical(PEOptions:-PURE),
                                        identical(PEOptions:-INTRINSIC),
                                        identical(PEOptions:-DYNAMIC)},
                                f   :: `procedure`)
                functions[eval(f)] := typ;
                thismodule;
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
