CodeCleanup := module()
    export
        RemoveDeadCodeSimple;
    local
        simpleAlg, cpair, findNames, simpleAlgLoop, hasName;


    RemoveDeadCodeSimple := proc(p) local m, _;
        if type(p, 'procedure') then
            m, _ := M:-ToM(ToInert(eval(p)));
            simpleAlg(m):-code;
        elif type(p, mform) then
            simpleAlg(p):-code;
        else
            error "argument must be of type procedure or mform, got %1", p;
        end if;
    end proc;


    simpleAlg := proc(m::mform, ns::set := {}, {loop := false})
        local h, names, q, n, c, t, e, i, res, res1, res2;

        names := ns;
        h := op(0, m);
        #print("simpleAlg", h, names);

        # case analysis on the statment type
        if h = MProc then
            res := procname(op(5, m), names);
            cpair(res:-names, subsop(5 = res:-code, m));

        elif h = MStatSeq then
            q := SimpleQueue();
            for i from 1 to nops(m) do
                res := procname(op(-i, m), names);
                if res:-code <> NULL then
                    q:-enqueue(res:-code);
                end if;
                #print("names", names);
                names := names union res:-names;
                #print("names2", names);
            end do;
            cpair(names, MStatSeq(op(ListTools:-Reverse(q:-toList()))))

        elif member(h, {MStandaloneExpr, MStandaloneFunction, MReturn, MError}) then
            cpair(findNames(m), m);

        elif typematch(m, MAssign('n'::mname, 'e'::mform))
        or   typematch(m, MAssignToTable('n'::mname, 'e'::mform))
        or   typematch(m, MAssignToFunction('n'::mname, 'e'::mform)) then


            if n= MGeneratedName("m4") then
               print("found it", names);
            end if;

            names := names union `if`(loop, {n}, {});
            if not hasName(n, names) then
                cpair(names, NULL);
            else
                cpair(names union findNames(e), m);
            end if;

        elif typematch(m, MAssignTableIndex(MTableref('n'::mname, 'c'::mform), 'e'::mform)) then
            #print("here", m);
            print(names);
            print();
            names := names union `if`(loop, {n}, {});
            if not hasName(n, names) then
                cpair(names, NULL);
            else
                cpair(names union findNames(e) union findNames(c), m);
            end if;


        elif typematch(m, MIfThenElse('c'::mform, 't'::mform, 'e'::mform)) then
            #print("MIfThenElse", c, t, e);
            res1 := procname(t, names);
            res2 := procname(e, names);
            cpair(res1:-names union res2:-names union findNames(c),
                  MIfThenElse(c, res1:-code, res2:-code));

        elif h = MCommand then
            cpair(names, NULL);

        elif h = MWhile then #loops
            simpleAlgLoop(m, names, 4)

        elif h = MWhileForFrom then
            simpleAlgLoop(m, names, 5)

        elif h = MWhileForIn then
            simpleAlgLoop(m, names, 3)

        else
            error "Unknown syntactic form %1", m; #cpair({}, m)
        end if
    end proc;

    hasName := (n, names) -> member(`if`(n::Local, MLocal(op(1,n)), n), names);


    simpleAlgLoop := proc(m, ns, num) local names, res;
        #print("simpleLoopAlg");
        names := ns;
        # first time is just to gather names
        res := simpleAlg(op(-1,m), names, loop=true);
        #print("sla", res:-names, names);
        res := simpleAlg(op(-1,m), names union res:-names); # for real this time
        names := names union foldl(`union`, op(map(findNames, [op(1..num, m)])));
        cpair(res:-names union names, subsop(-1 = res:-code, m));
    end proc;


    findNames := proc(e::mform) local names, found;
        #print("findNames", args);
        names := table();
        found := f -> proc(n)
                          names[f(n)] := 'blah';
                      end proc;

        eval(e, [MLocal = found(MLocal),
                 MParam = found(MLocal),
                 MSingleUse = found(MLocal),
                 MGeneratedName = found(MLocal),
                 MLexicalLocal = found(MLexicalLocal),
                 MLocalName = found(MLocalName),
                 MAssignedLocalName = found(MAssignedLocalName),
                 MName = found(MName),
                 MAssignedName = found(MAssignedName)
        ]);

        #print("what", indices(names));

        {op(map(op, [indices(names)]))};
    end proc;

    cpair := proc(n::set, c)
        if nargs = 1 then
            Record('code'=NULL, 'names'=n);
        else
            Record('code'=c, 'names'=n);
        end if;
    end proc;

end module:
