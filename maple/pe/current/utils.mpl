
printmod := proc(m)
    local oper, printit;
    kernelopts(opaquemodules=false);
    
    printit := proc(x)
        print(convert(x, string), x);
        print();
    end proc;
    
    if type(m, `module`) then
    
        # prints exports
        for oper in op(1, eval(m)) do
            printit(oper);
        end do;
        
        #prints locals
        for oper in op(3, eval(m)) do
            printit(oper);
        end do;
    else
        print(m);
    end if;
    
    kernelopts(opaquemodules=true);
    NULL;
end proc;


# returns a closure that generates unique names (as strings)
makeNameGenerator := proc(n::string)::procedure;
    local val;
    val := 0;
    return proc()
        val := val + 1;
        cat(n, val);
    end proc;
end proc;