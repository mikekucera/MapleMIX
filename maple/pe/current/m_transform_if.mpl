
TransformIfNormalForm := module()
    export ModuleApply;
    local indexOfFirstIf;

    # given a statment sequence returns the index of 
    # the first IF statment in the sequence
    indexOfFirstIf := proc(statseq::m(StatSeq))
        local index, i;
        index := FAIL;
        for i from 1 to nops(statseq) do
            if Header(op(i, statseq)) = MIfThenElse then
                index := i;
                break;
            end if;
        end do;
        index;
    end proc;


    # recursively performs program transformation
    ModuleApply := proc(m::m(StatSeq))
        local i;
        i := indexOfFirstIf(m);
        if i = FAIL then # there is no if statment
            return m;
        end if;    

        # break original statment sequence into three parts
        firstpart := op(1..i-1, m);
        ifstat    := op(i, m);
        rest      := op(i+1..-1, m);
            
        MStatSeq(firstpart,
                 MIfThenElse(op(1,ifstat),
                             procname(MStatSeq(op(2,ifstat), rest)),
                             procname(MStatSeq(op(3,ifstat), rest))
                            )
                )
    end proc;

end module;

