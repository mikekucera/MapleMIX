
M := module()
    export Print, ToM, FromM, ReduceExp, IsM, TransformIfNormalForm, Unfold,
           EndsWithReturn, FlattenStatSeq, AddImplicitReturns, UsesArgsOrNargs,
           Params, Locals, ProcBody, Header, Last, Front,
           Cond, Then, Else,
           ssop, remseq;
    local intrinsic, createTableProcs;
    
    # set of builtin function names
    intrinsic := {anames(builtin)};

    # returns true if the type is argument is an M form
    IsM := x -> evalb(type(x, m));    

    # returns three procs that apply their args to the given table of procs
    createTableProcs := proc(tbl)
        local toForm, toForm2, toFormMap;
        # takes one arg               
        toForm := code -> tbl[op(0, code)](op(code));
        # takes two args
        toForm2 := (y, z) -> (toForm(y), toForm(z));
        # takes any number of args
        toFormMap := () -> op(map(toForm, [args]));
        return toForm, toForm2, toFormMap;
    end proc;
    
        
    # used to print out M forms in a (slightly more) readable way
    Print := proc(m::m)
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
    
    # returns true if the given procedure body contains a use of MArgs or MNargs
    UsesArgsOrNargs := proc(m::m(StatSeq)) :: boolean;
        evalb(hasfun(m, {MNargs, MArgs}))    
    end proc;
    
    
    # returns true iff the given statment is a return or is a statseq that ends with a return
    EndsWithReturn := proc(m::m)
        if m = MStatSeq() then
            false;
        elif Header(m) = MStatSeq then
            procname(op(-1, FlattenStatSeq(m)));
        else
            evalb(Header(m) = MReturn);
        end if;
    end proc;
    
    # Only flattens the outermost statment sequence, does not recurse into structures such as ifs and loops
    FlattenStatSeq := proc(statseq::m(StatSeq)) ::m(StatSeq);
        local flatten;
        flatten := proc(m)
            `if`(Header(m)=MStatSeq, op(map(flatten,m)), m);
        end proc;    
        map(flatten, statseq);
    end proc:
    
        
    # If a statseq ends with an assignment, then an implicit return is added
    AddImplicitReturns := proc(statseq::m(StatSeq)) ::m(StatSeq);
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
    ssop := proc(m::m) option inline;
    	`if`(op(0,m) = MStatSeq, op(m), m)
    end proc;
    
    # if the argument is a MStatSeq consisting of a single statment,
    # then the MStatSeq is removed and the single statment is returned
    remseq := proc(m::m) option inline;
        `if`(op(0,m) = MStatSeq and nops(m) = 1, op(m), m)
    end proc;
    
    
    # TODO, proc that returns true if the body of the given MProc is a single statment
    
    
    Header   := proc(x) option inline; op(0,x) end proc:
    
    # generally for working with MStatSeq
    Last     := proc(x) option inline; op(-1, x) end proc;
    Front    := proc(x) option inline; op(1..-2, x) end proc;
    
    # for procs
    Params   := proc(x) option inline; op(1,x) end proc:
    Locals   := proc(x) option inline; op(2,x) end proc:
    ProcBody := proc(x) option inline; op(5,x) end proc:
    
    # for MIfThenElse
    Cond := proc(x) option inline; op(1, x) end proc;
    Then := proc(x) option inline; op(2, x) end proc;    
	Else := proc(x) option inline; op(3, x) end proc;
	
	

$include "m_tom.mpl"

$include "m_fromm.mpl"

$include "m_transform_if.mpl"

$include "m_unfold.mpl"

end module: