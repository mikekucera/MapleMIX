
printmod := proc(m)
    local oper, printit;
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

# these two procs arent really needed if you set opaquemodules=false
getma := proc(m)
	op(select(x->evalb(convert(x,string)="ModuleApply"), [op(3,eval(m))]));
end proc:


printma := proc(m)
    ma := getma(m);
    print(eval(ma));
    print();
end proc:



getlocal := proc(m::`module`, n)
    op(select(x->evalb(convert(x,string)=n), [op(3,eval(m))]));
end proc:
