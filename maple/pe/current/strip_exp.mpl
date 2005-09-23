
# the purpose of this module is to strip impure functions out
# of an expression and replace them with new variables

StripExp := module()
    description "strips impure function applications out of expressions";
    export strip;
    local intrinsic;

    # set of functions that should be treated like 'intrinsic' operations
    intrinsic := {"type", "op", "mod"};

    strip := proc(e::inert, gen::procedure)
        local examine_func, impure_funcs, res;        
 
        impure_funcs := [];  

        # generation of table is a side effect of nested proc
        examine_func := proc(f)
            local newvar;
            if member(op(1, f), intrinsic) then
                _Inert_FUNCTION(args);
            else
                newvar := gen();                
                impure_funcs := [op(impure_funcs), newvar = _Inert_FUNCTION(args)];
                _Inert_LOCAL(newvar);
            end if; 
        end proc;

        res := eval(e, [_Inert_FUNCTION = examine_func]);
        return impure_funcs, res;
    end proc;

end module;
