
M := module()
    export Print, ToM, FromM, ReduceExp, IsM, TransformIfNormalForm,
           Params, Locals, ProcBody, Header;
    local intrinsic, createTableProcs;
    
    # set of builtin function names
    intrinsic := {anames(builtin)};

    # returns true if the type is argument is an M form
    IsM := x -> evalb(type(x, m));    

    # returns three procs that apply their args to the given table of procs
    createTableProcs := proc(tbl)
        local toForm, toForm2, toFormMap;
        # takes one arg               
        toForm := code -> tbl[op(0, code)](op(code));
        # takes two args
        toForm2 := (y, z) -> (toForm(y), toForm(z));
        # takes any number of args
        toFormMap := () -> op(map(toForm, [args]));
        return toForm, toForm2, toFormMap;
    end proc;
    
        
    # used to print out M forms in a (slightly more) readable way
    Print := proc(m::m)
        printspaces := proc(num)
            from 1 to num*2 do printf(" ") end do
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
    
    Params   := proc(x) option inline; op(1,x) end proc:
    Locals   := proc(x) option inline; op(2,x) end proc:
    ProcBody := proc(x) option inline; op(5,x) end proc:
    Header   := proc(x) option inline; op(0,x) end proc:


$include "m_tom.mpl"

$include "m_fromm.mpl"

$include "if_transform.mpl"

$include "m_reduce_exp.mpl"

end module: