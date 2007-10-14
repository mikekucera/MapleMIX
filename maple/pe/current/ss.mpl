
SuperStack := module()
    description "Implementation of a Stack data-structure based on tables, has a more useful interface than SimpleStack.";
    export ModuleApply;

    ModuleApply := proc()
        module()
            local data, topIndex;
            export depth, empty, toList, push, pop, top, topDownIterator, find, each, init;

            data := table();
            topIndex := 0;

            init := proc()
                data := table();
                topIndex := 0;
            end proc;

            depth  := () -> topIndex;
            empty  := () -> evalb(topIndex = 0);
            toList := () -> [seq(eval(data[i],1), i=1..topIndex)];

            push := proc(x)
                topIndex := topIndex + 1;
                data[topIndex] := x;
            end proc;

            pop := proc() local temp;
                temp := `if`(topIndex=0, ERROR("empty stack"), data[topIndex]);
                data[topIndex] := evaln(data[topIndex]);
                topIndex := topIndex - 1;
                temp;
            end proc;

            top := proc()
                if topIndex = 0 then
                    error "empty stack"
                end if;
                data[topIndex];
            end proc;

            topDownIterator := proc() local i;
                i := topIndex;
                module() export getNext, hasNext;
                    getNext := proc() local temp;
                        temp := data[i];
                        i := i - 1;
                        temp;
                    end proc;
                    hasNext := () -> evalb(i>0);
                end module;
            end proc;

            find := proc(p::procedure, errormessage) local i, frame;
                for i from topIndex to 1 by -1 do
                    frame := data[i];
                    if p(frame) then
                        return frame;
                    end if
                end do;
                if nargs > 1 then
                    error op(errormessage);
                else
                    error "not found";
                end if;
            end proc;
            
            each := proc(f::procedure) local i;
                for i from topIndex to 1 by -1 do
                    f(data[i]);
                end do;
                NULL;
            end proc;

        end module;
    end proc;
end module:

SuperQueue := module()
    description "Implementation of a Queue data-structure based on tables, fixes a bug in SimpleQueue";
    export ModuleApply;

    ModuleApply := proc () 
    local lnargs, largs; 
    option `Copyright (c) 1999 Waterloo Maple Inc. All rights reserved.`; 
    largs := [args]; 
    lnargs := nargs; 
    module () 
        local i, data, headptr, tailptr; 
        export length, enqueue, dequeue, empty, map, clear, reverse, 
               front, toList, clone, isQueue; 

        data := table([seq(i = largs[i],i = 1 .. lnargs)]); 
        headptr := 1; 
        tailptr := lnargs; 
        isQueue := true; 

        length := () -> tailptr-headptr+1; 
        empty := () -> evalb(tailptr-headptr <= -1); 
        front := proc () 
            if tailptr < headptr then error "empty queue" end if; 
            eval(data[headptr],1) 
        end proc; 
        enqueue := proc (datum) 
            tailptr := 1+tailptr; 
            data[tailptr] := datum 
        end proc; 
        dequeue := proc () local t; 
            if tailptr < headptr then error "empty queue" end if; 
            t := data[headptr]; 
            data[headptr] := 'data[headptr]'; 
            headptr := 1+headptr; 
            eval(t,1) 
        end proc; 
        toList := proc () local k; 
            [seq(eval(data[k],1),k = headptr .. tailptr)] 
        end proc; 
        map := proc (p) SuperQueue(seq(p(data[i]),i = headptr .. tailptr)) end proc; 
        clear := proc () local j; 
            if not empty() then 
                for j from headptr to tailptr do 
                    data[j] := 'data[j]' 
                end do 
            end if; 
            headptr := 1; tailptr := 0;
        end proc; 
    end module;

    end proc:
end module:
