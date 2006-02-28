
CallStack := module()
    export ModuleApply;

    ModuleApply := proc()
        module()
            local 
                stack, getInfo, setInfo;
            export 
                push, pop, topEnv, 
                inConditional, setConditional,
                wasGlobalEnvUpdated, setGlobalEnvUpdated;

            stack := SimpleStack();

            # push and pop OnENVs but other important information 
            # is also stored in each frame
            
            push := proc(env := OnENV())
                local tbl;
                tbl := table();
                tbl["env"] := env;
                tbl["conditional"] := false;
                tbl["genvUpdated"] := false;
                stack:-push(tbl);
                NULL;
            end proc;

            pop := () -> stack:-pop()["env"];
            
            # access other information stored in each stack frame
            
            getInfo := proc(s::string)
                stack:-top()[s];
            end proc;
            
            setInfo := proc(s::string, x)
                stack:-top()[s] := x;
                NULL;
            end proc;

            topEnv := () -> getInfo("env");
            inConditional := () -> getInfo("conditional");
            wasGlobalEnvUpdated := () -> getInfo("genvUpdated");

            setConditional := proc(b::boolean := true)
                setInfo("conditional", b);
            end proc;
            
            setGlobalEnvUpdated := proc(b::boolean := true)
                setInfo("genvUpdated", b):
            end proc;

        end module;
    end proc;

end module;
