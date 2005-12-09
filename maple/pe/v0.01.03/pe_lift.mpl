
Lifter := module()
    export LiftExp, LiftPostProcess, liftStat, liftExp;

    liftStat := proc(stat) local t, e, c, n, f, s, b;
        h := Header(stat);
        if member(h, {MStatSeq, MCatchSeq}) then
            map(procname, stat)
        elif member(h, {MStandaloneExpr, MReturn}) then
            (h @ liftExp @ op)(stat)
        elif typematch(stat, MAssign('t'::anything, 'e'::anything)) then
            MAssign(liftExp(t), liftExp(e));
        elif typematch(stat, MSingleAssign('t'::anything, 'e'::anything)) then
            MSingleAssign(liftExp(t), liftExp(e));
        elif typematch(stat, MTableAssign('t'::anything, 'e'::anything)) then
            MTableAssign(liftExp(t), liftExp(e));
        elif typematch(stat, MAssignToFunction('s'::anything, 'e'::anything)) then
            MAssignToFunction(liftExp(s), liftExp(e));
        elif typematch(stat, MIfThenElse('c'::anything, 't'::anything, 'e'::anything)) then
            MIfThenElse(liftExp(c), procname(t), procname(e));
        elif typematch(stat, MStandaloneFunction('n'::anything, 'e'::anything)) then
            MStandaloneFunction(n, liftExp(e));
        elif typematch(stat, MTry('t'::anything, 'c'::anything, 'f'::anything)) then
            MTry(liftStat(t), liftStat(c), liftStat(f));
        elif typematch(stat, MTry('t'::anything, 'c'::anything)) then
            MTry(liftStat(t), liftStat(c));
        elif typematch(stat, MCatch('s'::anything, 'b'::anything)) then
            MCatch(s, liftStat(b));
        elif typematch(stat, MFunction('s'::anything, 'e'::anything)) then
            MFunction(liftExp(s), liftExp(e));
        else
            error "lifting of statement form %1 not supported", h
        end if;
    end proc;

    # Recurses through expressions and lifts where neccesary.
    # Also makes sure that expressions are embedded in MExpSeq where neccessary.
    liftExp := proc(exp) local t, i, s, e;
        if nargs = 0 then
            return MExpSeq() # lifting static NULL
        elif nargs > 1 then
            return MExpSeq(op(map(procname, [args])));
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
            MTableref(procname(t), MExpSeq(procname(i)));
        elif typematch(exp, MFunction('s'::anything, 'e'::anything)) then
            MFunction(procname(s), MExpSeq(procname(e)));
        elif type(exp, mform) then
            map(procname, exp);
        else
    	    M:-ToM(ToInert(exp));
    	end if;
    end proc;


    # Lifts all static values that are embedded in the residual code.
    # Meant to be used as a post-process.
    LiftPostProcess := proc(code::table)
        for pn in keys(code) do
            body := M:-ProcBody(code[pn]);
            code[pn] := subsop(5 = liftStat(body), code[pn]);
        end do;
        NULL;
    end proc;

end module;