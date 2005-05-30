# Simple online partial evaluator for a subset of maple
# Only works on simple expressions

OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    export pe;
    global `index/dyn`;
    local pe_main, onEnv, tblToList, replace, substitute, isVal, 
          reduceBody, paramFilter, localFilter, subsVars,
          getParams, getLocals, getStatSeq, getHeader, getVal;


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
    if not type(eval(p), 'procedure') then
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


# for extracting subexpressions from inert procedures
getParams := proc(x) option inline; op(1,x) end proc;
getLocals := proc(x) option inline; op(2,x) end proc;
getStatSeq := proc(x) option inline; op(5,x) end proc;

# for extracting subexpressions from inert statments
getHeader := proc(x) option inline; op(0,x) end proc;
getVal := proc(x) option inline; op(1,x) end proc;


pe_main := proc(p, env::table)
    local inert, body, params, locals,
          newParamList, newLocalList;

    # copy the initial environment
    onEnv := copy(env);
    # get the inert form of the procedure
    inert := ToInert(eval(p));

    params := getParams(inert);
    locals := getLocals(inert);
    body := getStatSeq(inert);

    # PREPROCESS
    body := subsVars(body, params, (i,v) -> _Inert_PARAM(i)=v);
    body := subsVars(body, locals, (i,v) -> _Inert_LOCAL(i)=v);
    newParamList := select(x -> onEnv[op(1,x)]=Dyn, getParams(inert));

    # PARTIAL EVALUATION
    body := map(reduceBody, body);

    # POSTPROCESS
    body := subsVars(body, newParamList, (i,v) -> v=_Inert_PARAM(i));

    newLocalList := select(x -> has(body,x), _Inert_LOCALSEQ(op(params),op(locals)) );
    body := subsVars(body, newLocalList, (i,v) -> v=_Inert_LOCAL(i));

    # unassign onEnv
    onEnv := 'onEnv';

    FromInert(subsop(1=newParamList, 2=newLocalList, 5=body, inert));
end proc;



# only supports assignemnts and some returns
reduceBody := proc(stmt) 
    local reduced, val;

    if isVal(getHeader(stmt)) then # implicit return of a value
        stmt;

    elif typematch(stmt, _Inert_NAME('n'::string)) then
        val := onEnv[n];
        if val = Dyn then stmt;
        else ToInert(val);
        end if;

    elif typematch(stmt, _Inert_ASSIGN(_Inert_NAME('n'::string), 'e'::anything)) then
        reduced := substitute(e);
        if isVal(reduced) then
            onEnv[n] := getVal(reduced);
            NULL;
        else
            onEnv[n] := Dyn;
            _Inert_ASSIGN(_Inert_NAME(n), reduced);
        end if;
    else
        error "not supported yet";
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
    member(op(0, e), {_Inert_INTPOS, _Inert_INTNEG, _Inert_STRING, _Inert_FLOAT, _Inert_RATIONAL});
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
