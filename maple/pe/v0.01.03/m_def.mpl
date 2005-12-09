
M := module()
    export Print, ToM, FromM, ReduceExp, TransformIfNormalForm, Unfold,
           EndsWithErrorOrReturn, FlattenStatSeq, AddImplicitReturns,
           SetArgsFlags, UsesArgsOrNargs, UsesArgs, UsesNargs,
           CreateLexMap,
           Params, Locals, ProcBody, Header, Last, Front,
           Cond, Then, Else,
           Try, CatchSeq, Finally,
           Var, IndexExp,
           ssop, remseq,
           intrinsic, variables, HasVariable;
    local createTableProcs, usesFlag, setFlag, createMap;

    # set of builtin function names
    intrinsic := {anames(builtin)};

    # mforms for variables
    variables := {MParam, MLocal, MGeneratedName, MSingleUse};

    HasVariable := proc(m::mform)
        hasfun(m, variables);
    end proc;

    # returns three procs that apply their args to the given table of procs
    createTableProcs := proc(tbl)
        local toForm, toForm2, toFormMap;
        # takes one arg
        toForm := proc(code)
            h := op(0, code);
            if assigned(tbl[h]) then
                return tbl[h](op(code));
            end if;
            error "%1 not supported", h
        end proc;
        # takes two args
        toForm2 := (y, z) -> (toForm(y), toForm(z));
        # takes any number of args
        toFormMap := () -> op(map(toForm, [args]));
        return toForm, toForm2, toFormMap;
    end proc;

    # used by ToM and FromM to create mapping tables
    createMap := proc(seq, yield::procedure)
        tbl := table();
        i := 1;
        for x in seq do
            yield(tbl, i, x);
            i := i + 1;
        end do;
        tbl;
    end proc;

    CreateLexNameMap := proc(lexicalseq::mform(LexicalSeq), f := (()->args))
        createMap(lexicalseq,
        proc(tbl, i, lexpair)
            tbl[op([1,1],lexpair)] := f(lexpair);
        end proc)
    end proc;

     # maps lexical indicies to their names
    createLexIndexMap := proc(lexicalseq)
        createMap(lexicalseq,
        proc(tbl, i, lexpair)
            tbl[i] := op([1,1], lexpair)
        end proc)
    end proc;


    # used to print out M forms in a (slightly more) readable way
    Print := proc(m::mform)
        printspaces := proc(num)
            from 1 to num*2 do printf(" ") end do
        end proc;
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
    end proc;


    SetArgsFlags := proc(p::mform(Proc)) :: mform(Proc);
        setFlag(setFlag(p, 1, MArgs), 2, MNargs);
    end proc;

    setFlag := proc(m, flag, fun)
        val := hasfun(m, fun);
        subsop([10,flag,1] = val, m);
    end proc;


    # returns true if the given procedure body contains a use of MArgs or MNargs
    UsesArgsOrNargs := proc(m::mform(Proc)) :: boolean;
        UsesArgs(m) or UsesNargs(m);
    end proc;

    # throws an exception
    UsesArgs := proc(m::mform(Proc)) :: boolean;
        evalb(usesFlag(m, 1));
    end proc;

    UsesNargs := proc(m::mform(Proc)) :: boolean;
        evalb(usesFlag(m, 2));
    end proc;

    usesFlag := proc(m, flag)
        val := op([10,flag,1], m);
        if val = UNKNOWN then
            error "query for " || flag || " set to UNKNOWN";
        end if;
        val;
    end proc;


    # returns true iff the given statment is a return or is a statseq that ends with a return
    EndsWithErrorOrReturn := proc(m::mform)
        if m = MStatSeq() then
            false;
        elif Header(m) = MStatSeq then
            procname(op(-1, FlattenStatSeq(m)));
        else
            evalb(member(Header(m), {MStatSeq, MError}));
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


    # If a statseq ends with an assignment, then an implicit return is added
    AddImplicitReturns := proc(statseq::mform(StatSeq)) ::mform(StatSeq);
        if statseq = MStatSeq() then
            return MStatSeq();
        end if;

        front := Front(statseq);
        last  := Last(statseq);
        header := Header(last);

        if member(header, {MAssign, MAssignToFunction}) then
            MStatSeq(front, last, MStandaloneExpr(op(1,last)));
        elif header = MIfThenElse then
            MStatSeq(front, MIfThenElse(Cond(last),
                                        procname(Then(last)),
                                        procname(Else(last))));
        else
            statseq;
        end if;
    end proc;


    # if the arg is a MStatSeq it gets converted into an expression sequence
    ssop := proc(m::mform) option inline;
    	`if`(op(0,m) = MStatSeq, op(m), m)
    end proc;

    # if the argument is a MStatSeq consisting of a single statment,
    # then the MStatSeq is removed and the single statment is returned
    remseq := proc(m::mform) option inline;
        `if`(op(0,m) = MStatSeq and nops(m) = 1, op(m), m)
    end proc;





    Header   := proc(x) option inline; op(0,x) end proc:

    # generally for working with MStatSeq
    Last     := proc(x) option inline; op(-1, x) end proc;
    Front    := proc(x) option inline; op(1..-2, x) end proc;

    # for procs
    Params    := proc(x) option inline; op(1,x) end proc:
    Locals    := proc(x) option inline; op(2,x) end proc:
    ProcBody  := proc(x) option inline; op(5,x) end proc:
    GlobalSeq := proc(x) option inline; op(7,x) end proc:
    LexSeq    := proc(x) option inline; op(8,x) end proc:

    # for MIfThenElse
    Cond := proc(x) option inline; op(1,x) end proc;
    Then := proc(x) option inline; op(2,x) end proc;
	Else := proc(x) option inline; op(3,x) end proc;

	# for MTableRef
	Var      := proc(x) option inline; op(1,x) end proc;
	IndexExp := proc(x) option inline; op(2,x) end proc;

    # for MTry
    Try      := proc(x) option inline; op(1,x) end proc;
    CatchSeq := proc(x) option inline; op(2,x) end proc;
    Finally  := proc(x) option inline; op(3,x) end proc;

    # for MCatch
    CatchString  := proc(x) option inline; op(1,x) end proc;
    CatchBody    := proc(x) option inline; op(2,x) end proc;

$include "m_tom.mpl"

$include "m_fromm.mpl"

$include "m_transform_if.mpl"

$include "m_unfold.mpl"

end module: