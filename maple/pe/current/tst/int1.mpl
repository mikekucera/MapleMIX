libname := libname, "lib":
kernelopts(opaquemodules=false):

int_pow := proc(x,var)
    if op(1,x)=var then
        if op(2,x)=-1 then
            LN(var)
        else
            var^(op(2,x)+1)/(op(2,x)+1)
        end if
    else
        MYINT(x,var)
    end if;
end proc:

int_sum := proc(l, var)
    local res, x;
    res := 0;
    for x in l do
        res := res + x[1]*int_pow(x[2],var);
    end do;
    res;
end proc:

goal := proc(n)
    local x;
    int_sum([[5,x^2], [-7,x^n], [2,x^(-1)]], x);
end proc:

res1 := OnPE(goal): 

print(res1:-ModuleApply);
res1(m);
