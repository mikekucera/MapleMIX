
M := module()
    export Print, ToM, ReduceExp;
    local mapitm, m, intrinsic, transformProcs;
    
    # set of builtin function names
    intrinsic := {anames(builtin)};

    isM := x -> evalb(type(x, m));    

    # used to print out M forms in a (slightly more) readable way
    Print := proc(m::m)
        printspaces := proc(num)
            from 1 to num*2 do
                printf(" ");
            end do;
        end proc;        
        doPrint := proc(indent, f)            
            if type(f, function) then
                printspaces(indent);
                printf("%a\n", op(0,f));              
                op(map(curry(procname, indent+1), [op(f)]));
            else 
                printspaces(indent);
                printf("%a\n", f);
            end if;
        end proc;        
        doPrint(0, m);        
    end proc;

    transformProcs := proc(tbl)
        local toForm, toForm2, toFormMap;
        # takes one arg               
        toForm := code -> tbl[op(0, code)](op(code));
        # takes two args
        toForm2 := (y, z) -> (toForm(y), toForm(z));
        # takes any number of args
        toFormMap := () -> op(map(toForm, [args]));

        return toForm, toForm2, toFormMap;
    end proc;
        

$include "m_tom.mpl"

$include "m_reduce_exp.mpl"

end module:

