
# the purpose of this module is to strip impure functions out
# of an expression and replace them with new variables

StripExp := module()
    description "strips function applications out of expressions";
    export strip;
    local intrinsic;

    # set of functions that should be treated like 'intrinsic' operations
    intrinsic := {anames(builtin)};


    strip := proc(e::inert, gen::procedure)
        local examine_func, impure_funcs, res;        
 
        q := SimpleQueue();  

        # generation of table is a side effect of nested proc
        examine_func := proc(f)
            local newvar;
            if member(convert(op(1, f), name), intrinsic) then
                _Inert_FUNCTION(args);
            else
                newvar := gen();    
                q:-enqueue(_Tag_ASSIGNTOFUNCTION(_Inert_LOCAL(newvar), _Inert_FUNCTION(args)));                
                _Inert_LOCAL(newvar);
            end if; 
        end proc;

        res := eval(e, [_Inert_FUNCTION = examine_func]);
        
        #return _Tag_STRIPPED(_Tag_STRIPPEDASSIGNSEQ(op(q:-toList())) _Tag_STRIPPEDEXPR(res));    
        
        return _Inert_STATSEQ(op(q:-toList())), _Tag_STRIPPEDEXPR(res);
        
    end proc;

end module;
