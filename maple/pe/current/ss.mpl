
SuperStack := module()
    export ModuleApply;

    ModuleApply := proc()
        module()
            local st, topIndex;
            export size, isEmpty, toList, push, pop, top, elementAt, topDownIterator, find;
            
            st := table();
    
            topIndex := 0;

            size := () -> topIndex;
            isEmpty := evalb(topIndex = 0);
            toList := () -> [seq(st[i], i=1..topIndex)];

            push := proc(x)
                topIndex := topIndex + 1;
                st[topIndex] := x;
            end proc;

            pop := proc()
                if topIndex = 0 then
                    error "empty stack"
                end if;
                temp := st[topIndex];
                st[topIndex] := evaln(st[topIndex]);
                topIndex := topIndex - 1;
                temp;
            end proc;

            top := proc()
                if topIndex = 0 then
                    error "empty stack"
                end if;
                st[topIndex];
            end proc;

            elementAt := proc(i)
                if assigned(st[i]) then
                    st[i];
                else
                    error "invalid index %1", i;
                end if
            end proc;
            
            topDownIterator := proc()
                i := topIndex;                
                module() export getNext, hasNext;
                    getNext := proc()
                        temp := st[i];
                        i := i - 1;
                        temp;
                    end proc;                
                    hasNext := () -> evalb(i>0);
                end module;    
            end proc;
            
            find := proc(p::procedure)
                for i from topIndex to 1 by -1 do
                    frame := st[i];
                    if p(frame) then
                        return frame;
                    end if
                end do;
                error "not found";
            end proc;

        end module;
    end proc;
end module:


