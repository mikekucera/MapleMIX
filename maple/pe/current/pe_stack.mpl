
CallStack := module()
    export ModuleApply;

    ModuleApply := proc()
        module()
            local stack, get;
            export push, pop, topEnv, inConditional, setConditional;

            stack := SimpleStack();

            push := proc(env := OnENV())
                local tbl;
                tbl := table();
                tbl["env"] := env;
                tbl["conditional"] := false;
                stack:-push(tbl);
                NULL;
            end proc;

            get := proc(s)
                stack:-top()[s];
            end proc;

            topEnv := () -> get("env");
            inConditional := () -> get("conditional");

            pop := proc() local tbl;
                tbl := stack:-pop();
                tbl["env"];
            end proc;

            setConditional := proc(b::boolean := true) local tbl;
                tbl := stack:-top();
                tbl["conditional"] := b;
                NULL;
            end proc;

        end module;
    end proc;

end module;
