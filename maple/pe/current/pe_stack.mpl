
CallStack := module()
    export New, ModuleApply;

    ModuleApply := New;

    New := proc()
        module()
            local stack, get;
            export push, pop, topEnv, inConditional, setConditional;

            stack := SimpleStack();

            push := proc(env := OnENV())
                if not stack:-empty() then
                    env:-setLink(stack:-top()["env"]);
                end if;
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

            pop := proc()
                tbl := stack:-pop();
                tbl["env"];
            end proc;

            setConditional := proc(b := true)
                tbl := stack:-top();
                tbl["conditional"] := b;
                NULL;
            end proc;

        end module;
    end proc;

end module;
