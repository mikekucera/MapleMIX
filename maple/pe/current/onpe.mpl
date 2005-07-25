
# Simple online partial evaluator for a subset of maple
# Only works on simple expressions


OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    export pe, makeGenerator;
    local EnvStack, gen;


##################################################################################


# returns a closure that generates unique names (as strings);
makeGenerator := proc() 
    local val;
    val := 0;
    return proc()
        val := val + 1;
        _Tag_GENNAME("x_" || val);
    end proc;
end proc;       

# for extracting subexpressions from inert procedures
getParams   := proc(x) option inline; op(1,x) end proc;
getLocals   := proc(x) option inline; op(2,x) end proc;
getProcBody := proc(x) option inline; op(5,x) end proc;

# for extracting subexpressions from inert statments
getHeader := proc(x) option inline; op(0,x) end proc;
getVal := proc(x) option inline; op(1,x) end proc;

isExpDynamic := x -> EvalExp:-isInert(x);
isExpStatic  := x -> not isExpDynamic(x);


subs_list := [
    _Inert_ASSIGN = pe_assign
];


# replaces params and local indices with their names
replace := proc(xs, f)
    i -> f(op(op(i, xs)));
end proc;

# returns a closure that maps param names to their indices
paramMap := proc(params)
    local tbl, i, c;
    tbl := table();
    c := 1;
    for i in params do
        tbl[op(i)] := c;
        c := c + 1;
    end do;

    return x -> _Inert_PARAM(tbl[x]);
end proc;


# returns two closures used to generate locals in the postprocess
localMap := proc()
    local tbl, rep, c, newLocals;
    tbl := table();
    c := 1;

    rep := proc(x)
        if not assigned(tbl[x]) then
            tbl[x] := c;
            c := c + 1;
        end if;        
        _Inert_LOCAL(tbl[x]);
    end proc;

    newLocals := proc()
        _Inert_LOCALSEQ(op(map(x -> _Inert_NAME(lhs(x)), op(eval(tbl)))));
    end proc;

    return rep, newLocals;
end proc;


# called with a procedure and a list of equations
pe := proc(p::procedure, statlist::list(anything=anything))
    local inert, body, params, locals,
          newParamList, newLocalList;

    gen := makeGenerator();

    #create initial environment
    env := OnENV:-NewOnENV();
    for eqn in statlist do
        env:-addVal(lhs(eqn),rhs(eqn));
    end do;

    EnvStack := SimpleStack();
    EnvStack:-push(env);

    # get the inert form of the procedure
    inert := ToInert(eval(p));
    params := getParams(inert);
    locals := getLocals(inert);
    body   := getProcBody(inert);

    #PRE-PROCESS, replace variable indices with names
    body := eval(body, [_Inert_PARAM = replace(params, _Inert_PARAM),
                        _Inert_LOCAL = replace(locals, _Inert_LOCAL)]);

    # PARTIAL EVALUATION
    body := eval(body, subs_list);

    # POST-PROCESS
    newParamList := select((env:-dynamic? @ getVal), params);
    paramReplace := paramMap(newParamList);
    localReplace, newLocals := localMap();    

    body := eval(body, [_Inert_PARAM = paramReplace, _Inert_LOCAL = localReplace]);
    
    newLocalList := newLocals();

    EnvStack := 'EnvStack';

    (subsop(1=newParamList, 2=newLocalList, 5=body, inert));    
end proc;



pe_assign := proc(name, expr)
    local assigns, stripped, reduced, inertAssigns;
    assigns, stripped := StripExp:-strip(expr, gen);
    
    # residualize all function calls for now
    inertAssigns := map(x -> _Inert_ASSIGN(lhs(x), rhs(x)), assigns);
    
    reduced := EvalExp:-reduce(stripped, EnvStack:-top());
    if isExpStatic(reduced) then
        env:-putVal(name, reduced);
        _Inert_STATSEQ(op(inertAssigns));
    else
       _Inert_STATSEQ(op(inertAssigns), _Inert_ASSIGN(name, reduced));
    end if;    
end proc;


end module;







p1 := proc(x, y)
    local z;
    z := x + y;
    return z;
end proc;
