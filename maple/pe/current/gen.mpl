
NameGenerator := module()
    export New, ModuleApply;

    # returns a closure that generates unique names (as strings)
    # this can be replaced later with something more fancy if necessary

    New := proc(n::string)::procedure;
        local val;
        val := 0;
        return proc()
            val := val + 1;
            cat(n, val);
        end proc;
    end proc;
    
    ModuleApply := New;

end module:
