    
M := module()
    export InertToM, Print;
    local mapitm, m, gen, intrinsic;
    
    # set of builtin function names
    intrinsic := {anames(builtin)};
    

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
        

$include "m_itom.mpl"

end module;

