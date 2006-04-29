#test

# TEST SUITE 1: BINARY POWERING #######################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "../lib":
#######################################################################


coefflist := proc(p) local l, i, cof, d;
    d := degree(p,x);
    return  [seq(coeff(p, x, d-i), i=0..d)];
end proc:

mydegree := proc(p, v)
    local lst, i, s;
    lst := coefflist(p, v);
    s := nops(lst);
    for i from 1 to s do
        if lst[i] <> 0 then
            return s-i
       end if;
   end do;
   return -infinity;
end proc:

goal := proc(a, b, c) local p;
    p := a*x^2+b*x+c;
    mydegree(p, x)
end proc;


opts := PEOptions();
opts:-setPropagateDynamic(true);
res1 := OnPE(goal, opts):


got := ToInert(eval(res1:-ModuleApply));

expected := ToInert(
proc(a, b, c)
    if a <> 0 then 2
    elif b <> 0 then 1
    elif c <> 0 then 0
    else -infinity
    end if
end proc
);

Try(100, got, expected);

#######################################################################




#######################################################################
#end test
