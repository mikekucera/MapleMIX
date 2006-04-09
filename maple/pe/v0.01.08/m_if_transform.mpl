
# the central idea of INF is that there is never code beneath a return
# this way I know that I can replace a return with an assignment and not change the meaning of the code

TransformIfNormalForm := module()
    description 
        "Program transformation for inert forms";
    export 
        ModuleApply;
    local 
        indexOfFirstIf, insertAtEnd, transform;


    # interface to module
    ModuleApply := proc(statseq::mform(StatSeq))
        transform(statseq);
    end proc;
    
    
    # given a statment sequence returns the index of the first IF statment in the sequence
    indexOfFirstIf := proc(statseq::mform(StatSeq)) local index, i;      
        index := FAIL;
        for i from 1 to nops(statseq) do
            if Header(op(i, statseq)) = MIfThenElse then
                index := i;
                break;
            end if;
        end do;
        index;
    end proc;


    # inserts 'toinsert' at the end of the given statment sequence 'stat'
    insertAtEnd := proc(stat::mform, toinsert::mform(StatSeq))
        if nops(stat) > 0 and Header(op(-1, stat)) = MReturn then
            stat;
        else
            MStatSeq(op(stat), op(toinsert))
        end if;
    end proc;
    
    
    # recursively performs program transformation
    transform := proc(mcode::mform(StatSeq)) local m, index, firstpart, ifstat, rest;
        m := FlattenStatSeq(mcode);
        index := indexOfFirstIf(m);
        if index = FAIL then # there is no if statment
            return m;
        end if;    

        # break original statment sequence into three parts
        firstpart := op(1..index-1, m);
        ifstat    := op(index, m);
        rest      := MStatSeq(op(index+1..-1, m));
        
        if not hasfun(ifstat, MReturn) then
            m
        elif nops(rest) > 0 then
            MStatSeq(firstpart, MIfThenElse(Cond(ifstat), 
                                  procname(insertAtEnd(Then(ifstat), rest)), 
                                  procname(insertAtEnd(Else(ifstat), rest))));
        else
            m;
        end if;
    end proc;

end module;
