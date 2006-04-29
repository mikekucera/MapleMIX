libname := libname, "lib":
kernelopts(opaquemodules=false):

int_pow := proc(i,var)
    if op(1,i)=var then
        if op(2,i)=-1 then
            LN(var)
        else
            var^(op(2,i)+1)/(op(2,i)+1)
        end if
    else
        MYINT(i,var)
    end if;
end proc:

int_sum := proc(l, var)
    local res, x, i;
    res := 0;
    #for x in l do
    for i from 1 to nops(l) do
        x := op(i, l);
        res := res + x[1]*int_pow(x[2],var);
        &onpe("print", "----------------------------------------------");
        &onpe("display");
    end do;
    res;
end proc:

goal := proc(n)
    local x;
    int_sum([[5,x^2], [-7,x^n], [2,x^(-1)]], x);
end proc:

opts := PEOptions();
opts:-setPropagateDynamic(true);
res1 := OnPE(goal, opts):

print(res1:-ModuleApply);
res1(m);
