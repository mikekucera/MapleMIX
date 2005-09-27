

TransformIfNormalForm := module()

    description "Program transformation for inert forms";
    export ModuleApply;
    local indexOfFirstIf, insertAtEnd, transform;


    # given a statment sequence returns the index of the first IF statment in the sequence
    
    indexOfFirstIf := proc(statseq::inert(STATSEQ))
        local index, i;
        index := FAIL;
        for i from 1 to nops(statseq) do
            if getHeader(op(i, statseq)) = _Inert_IF then
                index := i;
                break;
            end if;
        end do;
        index;
    end proc;



    # inserts 'toinsert' at the end of the given statment sequence 'stat'
    
    insertAtEnd := proc(toinsert::inert(STATSEQ), stat::inert({CONDPAIR, STATSEQ}))        
        if getHeader(stat) = _Inert_CONDPAIR then
            _Inert_CONDPAIR(op(1, stat), procname(toinsert, op(2, stat)));
        else
            _Inert_STATSEQ(op(stat), op(toinsert));
        end if;
    end proc;
    
    
    
    # recursively performs program transformation

    transform := proc(inert::inert({CONDPAIR, STATSEQ}))
        if getHeader(inert) = _Inert_CONDPAIR then
            return _Inert_CONDPAIR(op(1,inert), procname(op(2,inert)));
        end if;

        index := indexOfFirstIf(inert);
        if index = FAIL then # there is no if statment
            return inert;
        end if;    

        # break original statment sequence into three parts
        firstpart := op(1..index-1, inert);
        ifstat    := op(index, inert);
        rest      := _Inert_STATSEQ(op(index+1..-1, inert));

        if nops(rest) > 0 then        
            # add empty else if necessary
            if getHeader(op(-1, ifstat)) = _Inert_CONDPAIR then
                ifstat := _Inert_IF(op(ifstat), _Inert_STATSEQ());
            end if;
            
            ifstat := map(curry(insertAtEnd, rest), ifstat);              
        end if;

        _Inert_STATSEQ(firstpart, map(procname, ifstat));
    end proc;



    # interface to module
    
    ModuleApply := proc(statseq::inert(STATSEQ))
        transform(statseq);
    end proc;

end module;






#totransform := proc()
#    a := 1;
#    b := 2;
#    if a = b then
#        if a = b then
#            return 99;
#        elif a > b then
#            return 98;
#        else
#            return 97;
#        end if;
#    end if;
#    c := 9;
#end proc;
#
#test := proc()
#    inert := ToInert(eval(totransform));
#    statseq := getProcBody(inert);
#    transformed := TransformIfNormalForm(statseq);
#    print(transformed);
#    print();
#    inert := subsop(5=transformed, inert);
#    res := FromInert(inert);
#    print(eval(res));
#end proc;
