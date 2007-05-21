Header   := proc(x) option inline; op(0,x) end proc:


# for pairs
Fst := proc(x) option inline; op(1,x) end proc;
Snd := proc(x) option inline; op(2,x) end proc;

# for MStatic
SVal := proc(x::specfunc(anything, MStatic)) op(x) end proc;
# for MBoth
StaticPart := proc(x::mform(Both)) option inline; op(1,x) end proc;
DynamicPart := proc(x::mform(Both)) option inline; op(2,x) end proc;

# generally for working with MStatSeq
Last     := proc(x) option inline; op(-1, x) end proc;
Front    := proc(x) option inline; op(1..-2, x) end proc;

# for procs
Params    := proc(x) option inline; op(1,x) end proc:
Locals    := proc(x) option inline; op(2,x) end proc:
OptionSeq := proc(x) option inline; op(3,x) end proc:
ProcBody  := proc(x) option inline; op(5,x) end proc:
GlobalSeq := proc(x) option inline; op(7,x) end proc:
LexSeq    := proc(x) option inline; op(8,x) end proc:
Keywords  := proc(x) option inline; op(11,x) end proc:

# for MIfThenElse
Cond := proc(x) option inline; op(1,x) end proc;
Then := proc(x) option inline; op(2,x) end proc;
Else := proc(x) option inline; op(3,x) end proc;

CodeUpToPointer := proc(branch::mform(StatSeq))
    `if`(Header(Last(branch)) = MRef, 
            MStatSeq(Front(branch)), 
            branch)
end proc;

CodeBelow := proc(branch)
    `if`(Header(Last(branch)) = MRef, Last(branch), NULL);
end proc;


# for MSubst
DynExpr := proc(x) option inline; op(2,x) end proc;

# for MTableRef
Tbl      := proc(x) option inline; op(1,x) end proc;
Var      := proc(x) option inline; op(1,x) end proc;
IndexExp := proc(x) option inline; op(2,x) end proc;

# for MTry
Try      := proc(x) option inline; op(1,x) end proc;
CatchSeq := proc(x) option inline; op(2,x) end proc;
Finally  := proc(x) option inline; op(3,x) end proc;

# for MCatch
CatchString  := proc(x) option inline; op(1,x) end proc;
CatchBody    := proc(x) option inline; op(2,x) end proc;

# for dealing with closures
Lex  := proc(x) option inline; op(1,x) end proc;
Code := proc(x) option inline; op(2,x) end proc;

# for dealing with modules
Package := proc(x) option inline; op(1,x) end proc;
Member := proc(x) option inline; op(2,x) end proc;

# for variables
Name := proc(x) option inline; op(1,x) end proc;

# for MParamSpec
TypeAssertion := proc(x) option inline; op(2,x) end proc;
Default := proc(x) option inline; op(3,x) end proc;

#for queues
qtoseq := proc(q) option inline; op(q:-toList()) end proc;

# if the arg is a MStatSeq it gets converted into an expression sequence
ssop := proc(m::mform)
    if nargs = 0 then return NULL end if;
	`if`(op(0,m) = MStatSeq, op(m), m)
end proc;

# for looping over tables
keys := proc(tbl) option inline;
    map(op, [indices(tbl)])
end proc;

# the full eval here is needed because p could look like m[d] !
hasOption := proc(n::name, p::procedure)
    member(n, {op(3, eval(p))});
end proc;

esop := proc(x::mform(ExpSeq)) local res;
    res := op(x);
    if nops([res]) = 1 and Header(res) = MExpSeq then
        procname(res);
    else
        res;
    end if;
end proc;

# if the argument is an MSubst then the dynamic expression is returned
substop := x -> `if`(Header(x) = MSubst, DynExpr(x), x);

msop := proc(x) option inline;
    `if`(op(0,x)=MStatic, op(x), x);
end proc;