
`type/bte` := '`module`(put, putList, get, list, clone, setDynamic, dynamic?, static?, display)';
`type/equation` := anything=anything;


BTE := module()
    export NewBTE;

    NewBTE := proc(eqnlst::list(equation) := [])

        module()
            local bte;
            export put, putList, get,
                   list, clone, setDynamic, 
                   dynamic?, static?, display;

            bte := table(eqnlst);


            put := proc(x,y)
                bte[x] := y;
            end proc;

            get := x -> bte[x];

            setDynamic := proc(x)
                bte[x] := evaln(bte[x]);
            end proc;

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
            
        end module;

    end proc;
    
end module;