# Simple online partial evaluator for a subset of maple
# Only works on simple expressions

OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    export pe, isTrue, isFalse;
    global `index/dyn`;
    local pe_main, tblToList, replace, reduceBySubst, isVal, 
          substitute, reduceCondition,
          reduceStmt, reduceIf, subsVars,
          getParams, getLocals, getProcBody, getHeader, getVal, getCondition,
          EnvStack;

##################################################################################

# indexing function for online binding environment
# assigning a table entry to Dyn effectivley unassigns it

`index/dyn` := proc(Idx::list, Tbl::table, Entry::list)
    if nargs = 2 then
        if assigned(Tbl[op(Idx)]) then Tbl[op(Idx)];
        else Dyn;
        end if;
    elif Entry = [Dyn] then        
        Tbl[op1] := evaln(Tbl[Idx[1]]);
    else
        Tbl[op(Idx)] := op(Entry);
    end if;
end proc;


##################################################################################


pe := proc(p::procedure, env::table)
    if not op(op(1,env)) = dyn then
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
    s;
end proc;


# for extracting subexpressions from inert procedures
getParams   := proc(x) option inline; op(1,x) end proc;
getLocals   := proc(x) option inline; op(2,x) end proc;
getProcBody := proc(x) option inline; op(5,x) end proc;

# for extracting subexpressions from inert statments
getHeader := proc(x) option inline; op(0,x) end proc;
getVal := proc(x) option inline; op(1,x) end proc;

pe_main := proc(p::procedure, env::table)
    local inert, body, params, locals,
          newParamList, newLocalList;

    EnvStack := SimpleStack();
    EnvStack:-push(copy(env));

    # get the inert form of the procedure
    inert := ToInert(eval(p));

    params := getParams(inert);
    locals := getLocals(inert);
    body := getProcBody(inert);

    # PREPROCESS
    body := subsVars(body, params, (i,v) -> _Inert_PARAM(i)=v);
    body := subsVars(body, locals, (i,v) -> _Inert_LOCAL(i)=v);

    newParamList := select(x -> env[op(1,x)]=Dyn, params);

    # PARTIAL EVALUATION
    body := map(reduceStmt, body);

    # POSTPROCESS
    body := subsVars(body, newParamList, (i,v) -> v=_Inert_PARAM(i));

                              # member??
    newLocalList := select(x -> has(body,x), _Inert_LOCALSEQ(op(params),op(locals)) );
    body := subsVars(body, newLocalList, (i,v) -> v=_Inert_LOCAL(i));

    EnvStack := 'EnvStack';

    FromInert(subsop(1=newParamList, 2=newLocalList, 5=body, inert));
end proc;



# only supports assignemnts and some returns
reduceStmt := proc(stmt) 
    local reduced, header, env;

    header := getHeader(stmt);
    env := EnvStack:-top();

    if isVal(header) then # implicit return of a value
        stmt;
    
    elif typematch(stmt, _Inert_RETURN('e'::anything)) then
        reduced := reduceBySubst(e, env);
        _Inert_RETURN(reduced);

    elif typematch(stmt, _Inert_NAME('n'::string)) then
        if env[n] = Dyn then stmt;
        else ToInert(env[n]);
        end if;

    elif header = _Inert_IF then
        reduceIf(stmt);

    elif typematch(stmt, _Inert_ASSIGN(_Inert_NAME('n'::string), 'e'::anything)) then
        reduced := reduceBySubst(e, env);
        if isVal(reduced) then
            env[n] := getVal(reduced);
            NULL;
        else
            env[n] := Dyn;
            _Inert_ASSIGN(_Inert_NAME(n), reduced);
        end if;
    else
        error "not supported yet";
    end if;
end proc;


getCondition := proc(x) option inline; op(1,x); end proc;


isTrue := proc(stmt) 
    getHeader(stmt) = _Inert_NAME and getVal(stmt) = "true";
end proc;

isFalse := proc(stmt) 
    getHeader(stmt) = _Inert_NAME and getVal(stmt) = "false";
end proc;



reduceIf := proc(stmt) 
    local red, env, coll, reducedIf, finished;

    coll := SimpleStack();
    finished := false;
    env := copy(EnvStack:-top());

    red := proc(s) local branch, reducedCond;
        if finished then return NULL end if;

        if getHeader(s) = _Inert_CONDPAIR then
            reducedCond := reduceCondition(getCondition(s), env); # reduce the condition

            if isTrue(reducedCond) then
                finished := true; #stop processing other branches
                EnvStack:-push(copy(env));                
                branch := map(reduceStmt, op(2, s));
                coll:-push(EnvStack:-pop());
                return branch;

            elif isFalse(reducedCond) then
                return NULL;

            else # dynamic conditional
                #generate a condpair
                EnvStack:-push(copy(env));
                branch := map(reduceStmt, op(2, s));
                coll:-push(EnvStack:-pop());
                return _Inert_CONDPAIR(reducedCond, branch);
            end if;
        else
            EnvStack:-push(copy(env));
            branch := map(reduceStmt, s);
            coll:-push(EnvStack:-pop());
            return branch;
        end if;
    end proc;


    reducedIf := map(red, stmt);

    # collect environments and alter as neccessary

    if not op(0, op(1, reducedIf)) = _Inert_CONDPAIR then #strip away unneccesary inertif
        op(1, reducedIf);
    else
        reducedIf;
    end if;
end proc;


# replaces variables by their static values then simplifies
substitute := proc(active, env)
    local i, a;
    #eval(active, op(2, eval(env)));
    a := active;
    for i in indices(env) do
        a := subs([convert(i[1],name) = env[i[1]]], a);
    end do;
    return a;
end proc;

reduceBySubst := proc(stmt, env) 
    ToInert(eval(substitute(FromInert(stmt), env)));
end proc;


# need a better reducer for boolean conditions
reduceCondition := proc(stmt, env) 
    local res, b;
    res := (substitute(FromInert(stmt), env));

    # this is bad because situations like x=x won't get reduced to true
    b := evalb(res);
    res := ToInert(res);
    if has(res, _Inert_NAME) then
        res;
    else
        ToInert(b);        
    end if;
end proc;


isVal := proc(e) 
    member(op(0, e), {_Inert_INTPOS, _Inert_INTNEG, _Inert_STRING, _Inert_FLOAT, _Inert_RATIONAL});
end proc;


# converts a table into a list of equations
tblToList := proc(tbl, s) 
    op(op(tbl))[s];
end proc;

end module;

env1 := table(dyn, ["x" = 5]);

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

p5 := proc(x, y) local z; z := simplify(x, y); z := z + y; z; end proc;


env2 := table(dyn, ["x"=5, "y"=10]);
env3 := table(dyn, ["x"=5]);

p6 := proc(x, y, z)
    if x = y then
        return z;
    elif x > y then
        return x - y;
    else
        return y - x;
    end if;
end proc;
