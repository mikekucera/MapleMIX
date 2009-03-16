# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.

#builds a modle definition that contains the residual code
BuildModule := module()
    export ModuleApply;

    ModuleApply := proc(n::string, code::table)::inert;
        local locals, exports, procLocalIndex, processProc, moduleStatseq, inertModDef;
        # get a list of names of module locals
        # n will be the export so remove it from this list
        locals := remove(`=`, keys(code), n);

        # each non exported proc will need a local index
        procLocalIndex := 0;

        # will be mapped over each residualized procedure
        processProc := proc(eqn)
            local procName, p, lexicalLocals, body, lseq, f, processFuncCall;
            procName := lhs(eqn);
            p := rhs(eqn);
            p := CodeCleanup:-RemoveDeadCodeSimple(p);
            if gopts:-getInlineAssigns() then
                p := CodeCleanup:-InlineAssignsSimple(p);
            end if;
            p := M:-FromM( p );
            procLocalIndex := procLocalIndex + `if`(procName = n, 0, 1);

            lexicalLocals := []; #list of lexical pairs(equations) of local name to index

            # used to evaluate each name reference

            processFuncCall := proc(n)
                local localName, localIndex, lexicalIndex;
                if Header(n) = _Inert_ASSIGNEDNAME then
                    return _Inert_FUNCTION(args);
                end if;

                localName := op(1, n); # strip off the _Inert_NAME
                if localName = n then
                    localIndex := nops(lexicalLocals) + 1;
                else
                    if not member(localName, locals, 'localIndex') then #nasty!
                        return _Inert_FUNCTION(args); #error "%1 is not a module local", localName;
                    end if;
                end if;

                if member(localName=localIndex, lexicalLocals, 'lexicalIndex') then
                    subsop(1=_Inert_LEXICAL_LOCAL(lexicalIndex), _Inert_FUNCTION(args));
                else
                    lexicalLocals := [op(lexicalLocals), localName=localIndex];
                    subsop(1=_Inert_LEXICAL_LOCAL(nops(lexicalLocals)), _Inert_FUNCTION(args));
                end if;

            end proc;


            body := eval(ProcBody(p), _Inert_FUNCTION = processFuncCall);

            f := proc(e)
                _Inert_LEXICALPAIR(_Inert_NAME(lhs(e)),_Inert_LOCAL(rhs(e)));
            end proc;

            lseq := map(f, lexicalLocals);

            lexicalLocals := _Inert_LEXICALSEQ( op(lseq) );
            p := subsop(5=body, 8=lexicalLocals, p);

            _Inert_ASSIGN(_Inert_LOCAL( `if`(procName = n, nops(locals) + 1, procLocalIndex) ) ,p);
        end proc;

        moduleStatseq := _Inert_STATSEQ(op(map(processProc, op(op(code)))));
        locals := _Inert_LOCALSEQ(op(map(_Inert_NAME, [op(locals)])));
        exports := _Inert_EXPORTSEQ(_Inert_NAME(n));

        # get a bare bones inert module then substitute
        inertModDef := ToInert('module() end module');
        subsop(2 = locals, 4 = exports, 5 = moduleStatseq, inertModDef);
    end proc;
end module;
