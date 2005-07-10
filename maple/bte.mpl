
`type/bte` := '`module`(put, putList, get, list, clone, setDynamic, dynamic?, static?, display, has?, combine)';
`type/equation` := anything=anything;


BTE := module()
    export NewBTE;

    NewBTE := proc(eqnlst::list(equation))

        module()
            local bte;
            export put, putList, get,
                   list, clone, setDynamic, combine, 
                   dynamic?, static?, display, has?;

            bte := table(eqnlst);


            put := proc(x,y)
                bte[x] := y;
            end proc;

            get := x -> bte[x];

            setDynamic := proc(x)
                bte[x] := evaln(bte[x]);
            end proc;

            has? := x -> assigned(bte[x]);
            static? := x -> assigned(bte[x]);
            dynamic? := x -> not static?(x);
            list := () -> (op@@2)(bte);
            clone := () -> NewBTE(list());

            putList := proc(eqnlst::list(equation))
                local eqn;
                for eqn in eqnlst do
                    bte[lhs(eqn)] := rhs(eqn);
                end do;
            end proc;          
            
            display := proc()
                print('BTE'(list()));
            end proc;
            
            
            combine := proc(bte2::bte)
                local newbte, i;
                newbte := NewBTE([]);                
                for i in indices(bte) do                    
                    i:=op(i);
                    if bte2:-has?(i) and bte2:-get(i) = bte[i] then
                        newbte:-put(i, bte[i]);
                    end if;
                end do;
                newbte;
            end proc;
            
        end module;

    end proc;
    
end module;