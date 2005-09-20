


pe_test := proc(p::procedure, vallist::list(equation) := [], printinert := true)
    inert := OnPE:-PartiallyEvaluate(p, vallist);
    
    if printinert then
        InertForms:-Print(inert);
        print();
    end if;

    try
        m := FromInert(inert);
    catch:
        print("FromInert failed", lastexception);
        return;
    end try;
 

    print("before");
    print(eval(p));
    print();

    print("after");
    printmod(eval(m));
    print();

    return m;        
end proc:


# The partial evaluator dosen't support tables yet, for
# function call specialization to work all the procs below
# have to be named.

p1 := proc(x, y)
    local z;
    z := x + y;
    return z;
end proc;


p2 := proc(x, y)
    local z;
    z := x + p1(x, y) + 10;
    return z;
end proc;


p3 := proc(x, y::integer)
    local z;
    z := x + y;
    return z;
end proc;


p4 := proc(x, y, z)
    if x = y then
        return z;
    end if;
    return z;
end proc;

p5 := proc(x, y, z)
    if x = y then
        return x;
    elif p1(x,y) > 10 then
        return y;
    else
        return z;
    end if;
end proc;




p6 := proc(x, y)
    if p1(x,y) > 10 then
        if p1(x, y) > 100 then
            return "greater than 100";
        else
            return "less than 100";
        end if;
    else
        return "no";
    end if;
end proc;


p7 := proc(x)
    return x;
    return x;
end proc;


p8 := proc(x)
    if type(x, integer) then 
        return 1;
    end if;
    return 0;
end proc;

p9 := proc(x::integer)
    return p8(x);
end proc;


p10 := proc(x)
    if x > 10 then
        return 1;
    end if;
    return 0;
end proc;

p11 := proc(x)
    p10(x);
end proc;

p12 := proc(x, y)
    if x = y then
        return 1;
    elif x > 20 then
        return 2;
    else
        return 3;
    end if;
end proc;

p13 := proc(x, y)
    return x + y;
end proc;

p14 := proc(x, y)
    a := p13(x, 10);
    return a;
end proc;




pow := proc(x, n) 
    if n = 0 then
        return 1;
    else
        return x * pow(x, n-1);
    end if;
end proc;
