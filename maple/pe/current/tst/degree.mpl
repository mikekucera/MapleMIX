
libname := libname, "lib":
kernelopts(opaquemodules=false):

coefflist := proc(p) local l, i, cof, d;
    d := degree(p,x);
    # map((y,q)->coeff(q, x, d-y), [seq(i, i=0..d)], p);
    #l := [seq(coeff(p, x, d-i), i=0..d)];
    return  [seq(coeff(p, x, d-i), i=0..d)];
    #l := [];
    #for i from degree(p, x) to 0 by -1 do
    #    cof := coeff(p, x, i);
    #    l := [op(l), cof];
    #end do;
    #return l;
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

############################

goal2a := proc(a,b) local p; 
    p := a*x^17+b*x^12;
    mydegree(p, x);
end proc;

goal2b := proc(a,b) local p; 
    p := a*x^17+b*x^12+3*x;
    mydegree(p, x);
end proc;

goal2c := proc(a) local p; 
    p := (a-5)*x^17+(a^2-1)*x^12+3*x;
    mydegree(p, x);
end proc;

############################

# M:-Print(M:-ToM(ToInert(eval(coefflist))));

opts := PEOptions();
opts:-setPropagateDynamic(true);
res1 := OnPE(goal, opts):
print(res1:-ModuleApply);

res2 := OnPE(goal2a, opts):
print(res2:-ModuleApply);

res2 := OnPE(goal2b, opts):
print(res2:-ModuleApply);

res2 := OnPE(goal2c, opts):
print(res2:-ModuleApply);
