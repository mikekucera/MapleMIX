
TransformIfNormalForm := module()
    export ModuleApply;
    local indexOfFirstIf;

    # given a statment sequence returns the index of 
    # the first IF statment in the sequence
    indexOfFirstIf := proc(statseq::m(StatSeq))
        local index, i;
        index := FAIL;
        for i from 1 to nops(statseq) do
            if Header(op(i, statseq)) = MStatSeq then
                error "MStatSeq must be flattened";
            elif Header(op(i, statseq)) = MIfThenElse then
                index := i;
                break;
            end if;
        end do;
        index;
    end proc;


    # recursively performs program transformation
    # StatSeqs must be in flattened form
    
    ModuleApply := proc(m::m(StatSeq))
        local i;
        flat := FlattenStatSeq(m);
        i := indexOfFirstIf(flat);
        if i = FAIL then # there is no if statment
            return flat;
        end if;    

        # break original statment sequence into three parts
        firstpart := op(1..i-1, flat);
        ifstat    := op(i, flat);
        rest      := op(i+1..-1, flat);
            
        MStatSeq(firstpart,
                 MIfThenElse(Cond(ifstat),
                             procname(MStatSeq(ssop(Then(ifstat)), rest)),
                             procname(MStatSeq(ssop(Else(ifstat)), rest))
                            )
                )
    end proc;

end module;

