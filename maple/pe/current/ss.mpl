
SuperStack := module()
    description "Implementation of a Stack data-structure based on tables, has a more useful interface than SimpleStack.";
    export ModuleApply;

    ModuleApply := proc()
        module()
            local data, topIndex;
            export depth, empty, toList, push, pop, top, topDownIterator, find, init;

            data := table();
            topIndex := 0;

            init := proc()
                data := table();
                topIndex := 0;
            end proc;

            depth  := () -> topIndex;
            empty  := () -> evalb(topIndex = 0);
            toList := () -> [seq(data[i], i=1..topIndex)];

            push := proc(x)
                topIndex := topIndex + 1;
                data[topIndex] := x;
            end proc;

            pop := proc()
                if topIndex = 0 then
                    error "empty stack"
                end if;
                temp := data[topIndex];
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

            topDownIterator := proc()
                i := topIndex;
                module() export getNext, hasNext;
                    getNext := proc()
                        temp := data[i];
                        i := i - 1;
                        temp;
                    end proc;
                    hasNext := () -> evalb(i>0);
                end module;
            end proc;

            find := proc(p::procedure)
                for i from topIndex to 1 by -1 do
                    frame := data[i];
                    if p(frame) then
                        return frame;
                    end if
                end do;
                error "not found";
            end proc;

        end module;
    end proc;
end module:


