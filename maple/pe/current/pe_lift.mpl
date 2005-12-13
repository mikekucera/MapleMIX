
Lifter := module()
    local gen;
    export LiftExp, LiftPostProcess, liftStat, liftExp, liftTable;

    liftStat := proc(stat) local t, e, c, n, f, s, b, stmts;
        h := Header(stat);

        # first consider the cases that don't result in a call to liftExp
        if member(h, {MStatSeq, MCatchSeq}) then
            return map(procname, stat)
        elif typematch(stat, MTry('t'::anything, 'c'::anything, 'f'::anything)) then
            return MTry(procname(t), procname(c), procname(f));
        elif typematch(stat, MTry('t'::anything, 'c'::anything)) then
            return MTry(procname(t), procname(c));
        elif typematch(stat, MCatch('s'::anything, 'b'::anything)) then
            return MCatch(s, procname(b));
        end if;

        stmts := table();
        lift := curry(liftExp, stmts);
        if member(h, {MStandaloneExpr, MReturn}) then
            result := (h @ lift @ op)(stat);
        elif typematch(stat, MAssign('t'::anything, 'e'::anything)) then
            result := MAssign(lift(t), lift(e));
        elif typematch(stat, MSingleAssign('t'::anything, 'e'::anything)) then
            result := MSingleAssign(lift(t), lift(e));
        elif typematch(stat, MTableAssign('t'::anything, 'e'::anything)) then
            result := MTableAssign(lift(t), lift(e));
        elif typematch(stat, MAssignToFunction('s'::anything, 'e'::anything)) then
            result := MAssignToFunction(lift(s), lift(e));
        elif typematch(stat, MIfThenElse('c'::anything, 't'::anything, 'e'::anything)) then
            result := MIfThenElse(lift(c), procname(t), procname(e));
        elif typematch(stat, MStandaloneFunction('n'::anything, 'e'::anything)) then
            result := MStandaloneFunction(n, lift(e));
        elif typematch(stat, MFunction('s'::anything, 'e'::anything)) then
            result := MFunction(liftExp(s), lift(e));
        elif typematch(stat, MError('s'::anything)) then
            result := MError(lift(s));
        else
            error "lifting of statement form %1 not supported", h
        end if;

        q := SimpleQueue();
        for k in indices(stmts) do
            q:-enqueue(stmts[op(k)]);
        end do;

        `if`(q:-empty(), result, MStatSeq(qtoseq(q), result));
    end proc;

    # Recurses through expressions and lifts where neccesary.
    # Also makes sure that expressions are embedded in MExpSeq where neccessary.
    liftExp := proc(stmts::`table`, exp) local t, i, s, e, n;
        lift := curry(procname, stmts);
        if nargs = 1 then
            return MExpSeq() # lifting static NULL
        elif nargs > 2 then
            res := MExpSeq(op(map(lift, [args[2..nargs]])));
            return res;
        end if;

        h := Header(exp);
        if member(h, {MInt, MString, MParam, MName, MLocal, MGeneratedName,
                      MSingleUse, MAssignedName, MLocalName})
                      then
            exp;
        elif h = Closure then
            Code(exp);
        elif h = SPackageLocal then
            error "cannot lift a package local yet, coming soon";
        elif h = SArgs then
            MArgs();
        elif typematch(exp, MTableref('t'::anything, 'i'::anything)) then
            MTableref(lift(t), MExpSeq(lift(i)));
        elif typematch(exp, MFunction('s'::anything, 'e'::anything)) then
            MFunction(lift(s), MExpSeq(lift(e)));
        elif type(exp, mform) then
            map(lift, exp);
        elif typematch(exp, STable('n'::anything, 't'::anything)) then
            liftTable(stmts, n, t);
        else
    	    M:-ToM(ToInert(exp));
    	end if;
    end proc;


    liftTable := proc(stmts::`table`, tblName, tbl::`table`)
        lift := curry(liftExp, stmts);
        q := SimpleQueue();

        for key in keys(tbl) do
            s := MTableAssign(MTableref(tblName, MExpSeq(lift(key))), lift(tbl[key]));
            q:-enqueue(s);
        end do;

        stmts[tblName] := MStatSeq(qtoseq(q));
        return tblName;
    end proc;

    # Lifts all static values that are embedded in the residual code.
    # Meant to be used as a post-process.
    LiftPostProcess := proc(code::table)
        for pn in keys(code) do
            body := ProcBody(code[pn]);
            code[pn] := subsop(5 = liftStat(body), code[pn]);
        end do;
        NULL;
    end proc;

end module;
