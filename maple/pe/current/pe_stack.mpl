# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.

CallStack := module()
    export ModuleApply;

    ModuleApply := proc()
        module()
            local 
                stack, getInfo, setInfo;
            export 
                push, pop, topEnv, 
                wasGlobalEnvUpdated, setGlobalEnvUpdated;

            stack := SuperStack();

            # push and pop OnENVs but other important information 
            # is also stored in each frame
            
            push := proc(env := OnENV())
                local tbl;
                tbl := table();
                tbl["env"] := env;
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
            wasGlobalEnvUpdated := () -> getInfo("genvUpdated");
            
            setGlobalEnvUpdated := proc(b::boolean := true)
                setInfo("genvUpdated", b):
            end proc;

        end module;
    end proc;

end module;
