Header   := proc(x) option inline; op(0,x) end proc:

SVal := proc(x::specfunc(anything, MStatic)) op(x) end proc;

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

# for dealing with closures
Lex  := proc(x) option inline; op(1,x) end proc;
Code := proc(x) option inline; op(2,x) end proc;

# for dealing with modules
Package := proc(x) option inline; op(1,x) end proc;
Member := proc(x) option inline; op(2,x) end proc;

# for variables
Name := proc(x) option inline; op(1,x) end proc;


#for queues
qtoseq := proc(q) option inline; op(q:-toList()) end proc;

# if the arg is a MStatSeq it gets converted into an expression sequence
ssop := proc(m::mform) option inline;
	`if`(op(0,m) = MStatSeq, op(m), m)
end proc;

# for looping over tables
keys := proc(tbl) option inline;
    map(op, [indices(tbl)])
end proc;