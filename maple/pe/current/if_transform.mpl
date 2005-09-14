

indexOfFirstIf := proc(statseq::inert(STATSEQ))
    index := FAIL;
    for i from 1 to nops(statseq) do
        if getHeader(op(i, statseq)) = _Inert_IF then
            index := i;
            break;
        end if;
    end do;
    index;
end proc;



transformIfNormalForm := proc(statseq::inert(STATSEQ))
    index := indexOfFirstIf(statseq);
    if index = FAIL then
        return statseq
    end if;    

    ifstat := op(index, statseq);
    rest := _Inert_STATSEQ(op(index+1..-1, statseq));

    # add empty else if necessary
    if getHeader(op(-1, ifstat)) = _Inert_CONDPAIR then
        ifstat
    end if;

end proc;


p := proc()
    a := 1;
    b := 2;
    if a = b then
        return 99;
    end if;
    c := 9;
    return a + b + c;
end proc;

test := proc()
    inert := ToInert(eval(p));
    statseq := getProcBody(inert);
    transformed := transformIfNormalForm(statseq);
    print(transformed);
    print();
    inert := subsop(5=transformed, inert);
    res := FromInert(inert);
    print(eval(res));
end proc;
