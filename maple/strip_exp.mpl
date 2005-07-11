
# the purpose of this module is to strip impure functions out
# of an expression and replace them with new variables

StripExp := module()
    description "strips impure function applications out of expressions";
    export strip;
    local known_pure;

    # get a list of 'mathematical' functions from the system
    known_pure := FunctionAdvisor(known_functions, quiet);
    # add functions that are not mathematical but are known to be pure
    known_pure := [op(known_pure), type];


    strip := proc(e, gen)
        local examine_func, impure_funcs, res;        
 
        impure_funcs := [];  

        # generation of table is a side effect of nested proc
        examine_func := proc(f)
            local newvar;
            print(known_pure);

            if member(convert(op(f), name), known_pure) then
                _Inert_FUNCTION(args);
            else
                newvar := gen();                
                impure_funcs := [op(impure_funcs), newvar = _Inert_FUNCTION(args)];
                _Inert_NAME(newvar);
            end if; 
        end proc;

        res := eval(e, [_Inert_FUNCTION = examine_func]);
        return impure_funcs, res;
    end proc;

end module;