
printmod := proc(m)
    local printit, before, oper;
    before := kernelopts(opaquemodules=false);

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

    kernelopts(opaquemodules=before);
    NULL;
end proc:
