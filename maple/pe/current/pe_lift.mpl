# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.

# TODO: get rid of this whole module, its totally useless
Lifter := module()
    local gen;
    export LiftExp, LiftPostProcess, liftStat, liftExp, liftTable, liftStatic;

    liftStat := proc(stat) local l, b, r, t, e, c, n, f, s, w, stmts, lift, h, q, k, result;
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
        elif typematch(stat, MRef('r'::anything)) then
            return procname(r:-code); # TODO: is this right?
        end if;

        stmts := table();
        lift := curry(liftExp, stmts);
        if member(h, {MStandaloneExpr, MReturn}) then
            result := (h @ lift @ op)(stat);
        elif typematch(stat, MAssign('t'::anything, 'e'::anything)) then
            result := MAssign(lift(t), lift(e));
        elif typematch(stat, MSingleAssign('t'::anything, 'e'::anything)) then
            result := MSingleAssign(lift(t), lift(e));
        elif typematch(stat, MAssignTableIndex('t'::anything, 'e'::anything)) then
            result := MAssignTableIndex(lift(t), lift(e));
        elif typematch(stat, MAssignToFunction('s'::anything, 'e'::anything)) then
            result := MAssignToFunction(lift(s), lift(e));
        elif typematch(stat, MIfThenElse('c'::anything, 't'::anything, 'e'::anything)) then
            result := MIfThenElse(lift(c), procname(t), procname(e));
        elif typematch(stat, MStandaloneFunction('n'::anything, 'e'::anything)) then
            result := MStandaloneFunction(n, lift(e));
        elif typematch(stat, MFunction('s'::anything, 'e'::anything)) then
            result := MFunction(lift(s), lift(e));
        elif typematch(stat, MError('s'::anything)) then
            result := MError(lift(s));
        elif typematch(stat, MWhileForFrom('l'::anything, 'f'::anything, 'b'::anything,
                                           't'::anything, 'w'::anything, 's'::anything)) then
            result := MWhileForFrom(lift(l), lift(f), lift(b), lift(t), lift(w), procname(s));
        else
            error "lifting of statement form %1 not supported", h
            # TODO, make sure all statment forms are here
        end if;

        q := SimpleQueue();
        for k in indices(stmts) do
            q:-enqueue(stmts[op(k)]);
        end do;

        `if`(q:-empty(), result, MStatSeq(qtoseq(q), result));
    end proc;

    # Recurses through expressions and lifts where neccesary.
    # Also makes sure that expressions are embedded in MExpSeq where neccessary.
    liftExp := proc(stmts::`table`, exp) local t, i, s, e, n, lift, h;
        lift := curry(procname, stmts);
        h := Header(exp);
        
        if member(h, {MInt, MString, MParam, MName, MLocal, MGeneratedName,
                      MSingleUse, MAssignedName, MLocalName, MLexicalLocal}) then
            exp;
        elif h = MStatic then
            if nops(exp) = 0 then
                MExpSeq()
            elif nops(exp) > 1 then
                MExpSeq(op(map(curry(liftStatic,stmts), [op(exp)])));
            else
                liftStatic(stmts, op(exp));
            end if;
        elif h = MBoth then
            DynamicPart(exp);
        elif typematch(exp, MTableref('t'::anything, 'i'::anything)) then
            MTableref(lift(t), MExpSeq(lift(i)));
        elif typematch(exp, MFunction('s'::anything, 'e'::anything)) then
            MFunction(lift(s), MExpSeq(lift(e)));
        elif typematch(exp, MSubst('n'::anything, 'e'::anything)) then
            MSubst(n, lift(e));
        elif exp::Dynamic then
            map(lift, exp);
        else
    	    error "static value not embedded in MStatic: %1", exp;
    	end if;
    end proc;


    liftStatic := proc(stmts::`table`, exp::Static) local n, t;
        if type(exp, 'procedure') then
            if Builtins:-isBuiltin(exp) then
                MStatic(Builtins:-getName(exp))
            else
                MStatic(exp);
            end if;
	    elif Header(h) = SPackageLocal then 
	        error "cannot lift a package local yet"
	    elif typematch(exp, STable('n'::anything, 't'::anything)) then
            liftTable(stmts, n, t);
        else
            MStatic(exp);
        end if;
    end proc;

    
    liftTable := proc(stmts::`table`, tblName, tbl::`table`) local key, q, s;
        q := SimpleQueue();

        for key in keys(tbl) do
            s := MAssignTableIndex(MTableref(tblName, MExpSeq(embed(key))), embed(tbl[key]));
            q:-enqueue(s);
        end do;

        stmts[tblName] := MStatSeq(qtoseq(q));
        return tblName;
    end proc;
    

    # Lifts all static values that are embedded in the residual code.
    # Meant to be used as a post-process.
    LiftPostProcess := proc(code::table) local pn, body;
        for pn in keys(code) do
            body := ProcBody(code[pn]);
            code[pn] := subsop(5 = liftStat(body), code[pn]);
        end do;
        NULL;
    end proc;

end module;
