
# the central idea of INF is that there is never code beneath a return
# this way I know that I can replace a return with an assignment and not change the meaning of the code

TransformIf := module()
    description 
        "Program transformation for inert forms";
    export 
        TransformToReturnNormalForm, TransformToDAG;
    local 
        indexOfFirstIf, insertAtEnd;

    
    
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
    insertAtEnd := proc(stat::mform(StatSeq), toinsert::mform)
        if nops(stat) > 0 and Header(op(-1, stat)) = MReturn then
            stat;
        elif Header(toinsert) = MStatSeq then
            MStatSeq(op(stat), op(toinsert))
        else
            MStatSeq(op(stat), toinsert)
        end if;
    end proc;
    
    
    # recursively performs program transformation
    TransformToReturnNormalForm := proc(mcode::mform(StatSeq)) 
        local m, index, firstpart, ifstat, rest;
        m := FlattenStatSeq(mcode);
        index := indexOfFirstIf(m);
        if index = FAIL then # there is no if statment
            return m;
        end if;    

        # break original statment sequence into three parts
        firstpart := op(1..index-1, m);
        ifstat    := op(index, m);
        rest      := MStatSeq(op(index+1..-1, m));
        
        
        if not hasfun(ifstat, MReturn) then # TODO, why this test?
            m
        elif nops(rest) > 0 then
            MStatSeq(firstpart, MIfThenElse(Cond(ifstat), 
                                  procname(insertAtEnd(Then(ifstat), rest)), 
                                  procname(insertAtEnd(Else(ifstat), rest))));
        else
            m;
        end if;
    end proc;

    
    TransformToDAG := proc(mcode::mform({StatSeq, Proc})) 
        local m, index, firstpart, ifstat, rest, ref;
        #print("transformToDAG", args);
        if Header(mcode) = MProc then
            return subsop(5=procname(ProcBody(mcode)), mcode);
        end if;
        
        
        m := FlattenStatSeq(mcode);
        index := indexOfFirstIf(m);
        if index = FAIL then # there is no if statment
            return m;
        end if;
        
        # break original statment sequence into three parts
        firstpart := op(1..index-1, m);
        ifstat    := op(index, m);
        rest      := MStatSeq(op(index+1..-1, m));
        #print("firstpart", firstpart, "ifstat", ifstat, "rest", rest);
        
        if nops(rest) > 0 then
            ref := MRef(Record('code'=procname(rest)));
            MStatSeq(firstpart, MIfThenElse(Cond(ifstat), 
                                  procname(insertAtEnd(Then(ifstat), ref)), 
                                  procname(insertAtEnd(Else(ifstat), ref))));
        else
            m;
        end if;
    
    end proc;
end module;
