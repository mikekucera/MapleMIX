
M := module()
    export Print,
           HasVariable, CreateLexNameMap,
           SetArgsFlags, UsesArgsOrNargs, UsesArgs, UsesNargs,
           ProtectedForm, EndsWithErrorOrReturn, FlattenStatSeq,
           IsNoOp, RemoveUselessStandaloneExprs, AddImplicitReturns,
           ToM, FromM, TransformIf;
    local
$include "access_header.mpl"
          intrinsic, isIntrinsic, variables, inertTrue, inertDollar,
          createTableProcs, createMap, usesFlag;

$include "access.mpl"


    # set of builtin function names
    intrinsic := {anames(builtin), 'curry', 'table', 'rand'} minus {'print'};
    isIntrinsic := x -> member(convert(x, name), intrinsic);

    # constants for easy access to common inert forms
    inertTrue := _Inert_NAME("true", _Inert_ATTRIBUTE(_Inert_NAME("protected", _Inert_ATTRIBUTE(_Inert_NAME("protected")))));
    inertDollar := _Inert_ASSIGNEDNAME("$","PROC",_Inert_ATTRIBUTE(_Inert_NAME("protected",_Inert_ATTRIBUTE(_Inert_NAME("protected")))));    

    # returns true iff the given mform contains the mform of a variable
    HasVariable := proc(m::mform)
        hasfun(m, {MName, MAssignedName, MCatenate, MLocal, MGenertatedName, MParam, MSingleUse});
    end proc;



    # Returns three procs that are used for the table displatch pattern in ToM and FromM
    createTableProcs := proc(n::string, tbl)
        local toForm, toForm2, toFormMap;

        # takes one arg
        toForm := proc(code) local h;
            h := op(0, code);
            if assigned(tbl[h]) then
                return tbl[h](op(code));
            end if;
            error cat(n, ", %1 not supported"), h;
        end proc;

        # takes two args
        toForm2 := (y, z) -> (toForm(y), toForm(z));

        # takes any number of args
        toFormMap := () -> op(map(toForm, [args]));

        return eval(toForm), eval(toForm2), eval(toFormMap);
    end proc;



    # Used to map a procedure over a sequence in order to create a table from it
    # the given procedure must modify the table tbl
    createMap := proc(seq, yield::procedure) local tbl, i, x;
        tbl := table();
        i := 1;
        for x in seq do
            yield(tbl, i, x);
            i := i + 1;
        end do;
        tbl;
    end proc;


    # Takes a lexical sequence and create a table mapping the name of
    # each lexical to f(lexpair)
    CreateLexNameMap := proc(lexicalseq::mform(LexicalSeq), f := (()->args))
        createMap(lexicalseq,
            proc(tbl, i, lexpair)
                tbl[op([1,1],lexpair)] := f(lexpair);
            end proc)
    end proc;


    # used to print out M forms in a (slightly more) readable way
    Print := proc(m::mform) local printspaces, doPrint;
        printspaces := proc(num)
            from 1 to num*2 do printf(" ") end do
        end proc;
        # recursive function that prints out the mform
        doPrint := proc(indent, f)
            if type(f, function) then
                printspaces(indent);
                printf("%a\n", op(0,f));
                op(map(curry(procname, indent+1), [op(f)]));
            else
                printspaces(indent);
                printf("%a\n", f);
            end if;
        end proc;
        doPrint(0, m);
        NULL;
    end proc;


    # Sets two flags in the mform of a proc that indicates if the
    # proc uses the args or nargs keywords. This is done because
    # checking for the use of MArgs or MNargs is otherwise costly.
    SetArgsFlags := proc(p::mform(Proc)) :: mform(Proc);
        local setFlag;
        setFlag := proc(m, flag, fun) local val;
            val := hasfun(m, fun);
            subsop([10,flag,1] = val, m);
        end proc;
        setFlag(setFlag(p, 1, MArgs), 2, MNargs);
    end proc;


    # returns true iff the given procedure body contains a use of MArgs or MNargs
    UsesArgsOrNargs := proc(m::mform(Proc)) :: boolean;
        UsesArgs(m) or UsesNargs(m);
    end proc;


    # returns true iff the given procedure body contains the use of MArgs
    UsesArgs := proc(m::mform(Proc)) :: boolean;
        evalb(usesFlag(m, 1));
    end proc;

    UsesNargs := proc(m::mform(Proc)) :: boolean;
        evalb(usesFlag(m, 2));
    end proc;

    # returns true iff the given procedure body contains the use of MNargs
    usesFlag := proc(m, flag) local val;
        val := op([10,flag,1], m);
        if val = UNKNOWN then
            error "query for %1 set to UNKNOWN", flag;
        end if;
        val;
    end proc;

    # returns the protected form of the given name
    ProtectedForm := proc(n::string)
        MAssignedName(n, "PROC", MAttribute(MName("protected", MAttribute(MName("protected")))))
    end proc;


    # returns true iff the given statment is a return or is a statseq that ends with a return
    EndsWithErrorOrReturn := proc(m::mform) local flat;
        if m = MStatSeq() then
            false;
        elif Header(m) = MStatSeq then
            flat := FlattenStatSeq(m);
            if flat = MStatSeq() then
                return false;
            end if;
            procname(op(-1, flat));
        else
            evalb(member(Header(m), {MReturn, MError}));
        end if;
    end proc;

    # Only flattens the outermost statment sequence, does not recurse into structures such as ifs and loops
    FlattenStatSeq := proc(statseq::mform(StatSeq)) ::mform(StatSeq);
        local flatten;
        flatten := proc(m)
            `if`(Header(m)=MStatSeq, op(map(flatten,m)), m);
        end proc;
        map(flatten, statseq);
    end proc:


    IsNoOp := proc(m::mform)
        m = MStatSeq() or 
        m = MStatSeq(MStandaloneExpr(MExpSeq())) or
        m = MStatSeq(MStatSeq()) or
        m = MStatSeq(MExpSeq()) or
        m = MStatSeq(MStatSeq(MExpSeq()))
    end proc;

    # removes standalone exprs that are not at the end of a statment sequence
    RemoveUselessStandaloneExprs := proc(statseq::mform(StatSeq))
        local ss, q, size, i, stat;
        ss := FlattenStatSeq(statseq);
        q := SimpleQueue();
        size := nops(ss);
        i := 1;
        for stat in ss do
            if Header(stat) <> MStandaloneExpr or i = size then
                q:-enqueue(stat);
            end if;
            i := i + 1;
        end do;
        MStatSeq(qtoseq(q));
    end proc;


    # If a statseq ends with an assignment, then an implicit return is added
    AddImplicitReturns := proc(stat::mform({StatSeq, IfThenElse}))
        local front, last, header;

        if stat = MStatSeq() then
            return MStatSeq();
        end if;

        if Header(stat) = MIfThenElse then
            return MIfThenElse(Cond(stat), procname(Then(stat)), procname(Else(stat)));
        end if;

        front := Front(stat);
        last  := Last(stat);
        header := Header(last);

        if header = MStatSeq then
            MStatSeq(front, procname(last));
        elif member(header, {MAssign, MAssignToFunction, MAssignTableIndex, MAssignToTable}) then
            MStatSeq(front, last, MStandaloneExpr(op(1,last)));
        elif header = MIfThenElse then
            MStatSeq(front, MIfThenElse(Cond(last),
                                        procname(Then(last)),
                                        procname(Else(last))));
        else
            stat;
        end if;
    end proc;



$include "m_tom.mpl"
$include "m_fromm.mpl"
$include "m_if_transform.mpl"

end module:
