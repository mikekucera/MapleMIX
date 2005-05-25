# Simple online partial evaluator for a subset of maple
# Only works on simple expressions

OnPE := module()
    export pe;
    global `index/dyn`;
    local pe_main, onEnv, tblToList, replace, substitute, isVal, reduceBody, paramFilter, localFilter, subsVars;


##################################################################################

# indexing function for online binding environment
# assigning a table entry to Dyn effectivley unassigns it

`index/dyn` := proc(Idx::list, Tbl::table, Entry::list)
    local op1;
    if nargs = 2 then
        if assigned(Tbl[op(Idx)]) then Tbl[op(Idx)];
        else Dyn;
        end if;
    elif Entry = [Dyn] then        
	op1 := Idx[1];
        Tbl[op1] := evaln(Tbl[op1]);
    else
        Tbl[op(Idx)] := op(Entry);
    end if;
end proc;


##################################################################################


pe := proc(p, env::table)
    if not whattype(eval(p)) = procedure then
        error "Currently only partial evaluation of single procedures is supported";
    elif not op(op(1,env)) = dyn then
        error "Only index/dyn tables allowed!";
    end if;

    pe_main(p, env);
end proc;

# used for substitutions in the preprocess and postprocess
subsVars := proc(sub, coll, f) 
    local s, c, var;
    s := sub;
    c := 1;
    for var in coll do
        s := subs([f(c,var)], s);
        c := c + 1;
    end do;
    return s;
end proc;


pe_main := proc(p, env::table)
    local inert, body, newParamList, newLocalList;

    # copy the initial environment
    onEnv := copy(env);
    # get the inert form of the procedure
    inert := ToInert(eval(p));
    body := op(5, inert);

    # PREPROCESS
    body := subsVars(body, op(1, inert), (i,v) -> _Inert_PARAM(i)=v);
    body := subsVars(body, op(2, inert), (i,v) -> _Inert_LOCAL(i)=v);
    newParamList := map(paramFilter, op(1,inert));

    # PARTIAL EVALUATION
    body := map(reduceBody, body);

    # POSTPROCESS
    body := subsVars(body, newParamList, (i,v) -> v=_Inert_PARAM(i));

    newLocalList := map(x -> localFilter(body,x), _Inert_LOCALSEQ(op(op(1,inert)),op(op(2,inert))));
    body := subsVars(body, newLocalList, (i,v) -> v=_Inert_LOCAL(i));

    # unassign onEnv
    onEnv := 'onEnv';

    FromInert(subsop(1=newParamList, 2=newLocalList, 5=body, inert));
end proc;


# filters out parameters that are static
paramFilter := proc(param)
    if onEnv[op(1,param)] = Dyn then param
    else NULL
    end if; 
end proc;


# filters out unneeded locals
localFilter := proc(body, loc)
    if has(body, loc) then loc
    else NULL
    end if;
end proc;


# only supports assignemnts and some returns
reduceBody := proc(stmt) 
    local head, reduced, val;

    head := op(0, stmt);

    if isVal(head) then # implicit return of a value
        stmt;
    elif head = _Inert_NAME then # implicit return of a name
        val := onEnv[op(1, stmt)];
        if val = Dyn then stmt;
        else ToInert(val);
        end if;
    elif head = _Inert_ASSIGN then         
        reduced := substitute(op(2, stmt));
        if isVal(reduced) then
            onEnv[op(1,op(1,stmt))] := op(1, reduced);
            NULL;
        else
            onEnv[op(1,op(1,stmt))] := Dyn;
            _Inert_ASSIGN(op(1,stmt), reduced);
        end if;
    else
        error cat(head, " not supported yet");
    end if;
end proc;


# replaces variables by their static values then simplifies
substitute := proc(stmt) 
    local i, active;
    active := FromInert(stmt);
    for i in indices(onEnv) do
        active := subs([convert(i[1],name) = onEnv[i[1]]], active);
    end do;
    ToInert(active);
end proc;


isVal := proc(e) 
    member(op(0, e), {_Inert_INTPOS, _Inert_INTNEG, _Inert_STRING, _Inert_Float, _Inert_RATIONAL});
end proc;


# converts a table into a list of equations
tblToList := proc(tbl, s) 
    op(op(tbl))[s];
end proc;


end module;


p1 := proc(x, y)
    local z;
    z := x + x * y;
    z;
end proc;

p2 := proc(x, y)
    local a, b;
    a := x + x;
    b := a * x;
    b;
end proc;

p3 := proc(x, y)
    local a, b;
    a := x + x;
    x := a * y; # x becomes dynamic
    x;
end proc;

p4 := proc(x, y)
    local a, b;
    y := x * x; # y becomes static
    y;
end proc;



testEnv := table(dyn, ["x" = 5]);
