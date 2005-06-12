
# Simple online partial evaluator for a subset of maple
# Only works on simple expressions


OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    export pe;
    local pe_main, tblToList, replace, reduceBySubst, isVal, 
          substitute, reduceCondition,
          reduceStmt, reduceIf, subsVars, isTrue, isFalse,
          getParams, getLocals, getProcBody, getHeader, getVal, getCondition,
          EnvStack;


##################################################################################



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



pe := proc(p::procedure, env::bte)
    local inert, body, params, locals,
          newParamList, newLocalList;

    EnvStack := SimpleStack();
    EnvStack:-push(env:-clone());

    # get the inert form of the procedure
    inert := ToInert(eval(p));

    params := getParams(inert);
    locals := getLocals(inert);
    body := getProcBody(inert);

    # PREPROCESS
    body := subsVars(body, params, (i,v) -> _Inert_PARAM(i)=v);
    body := subsVars(body, locals, (i,v) -> _Inert_LOCAL(i)=v);

    newParamList := select((env:-dynamic? @ getVal), params);

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
        if env:-dynamic?(n) then stmt;
        else ToInert(env:-get(n));
        end if;

    elif header = _Inert_IF then
        reduceIf(stmt);

    elif typematch(stmt, _Inert_ASSIGN(_Inert_NAME('n'::string), 'e'::anything)) then
        reduced := reduceBySubst(e, env);
        if isVal(reduced) then
            env:-put(n, getVal(reduced));
            NULL;
        else
            env:-setDynamic(n);
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
    env := EnvStack:-top();

    red := proc(s) local branch, reducedCond;
        if finished then return NULL end if;

        if getHeader(s) = _Inert_CONDPAIR then
            reducedCond := reduceCondition(getCondition(s), env); # reduce the condition

            if isTrue(reducedCond) then
                finished := true; #stop processing other branches
                EnvStack:-push(env:-clone());                
                branch := map(reduceStmt, op(2, s));
                coll:-push(EnvStack:-pop());
                return branch;

            elif isFalse(reducedCond) then
                return NULL;

            else # dynamic conditional
                #generate a condpair
                EnvStack:-push(env:-clone());
                branch := map(reduceStmt, op(2, s));
                coll:-push(EnvStack:-pop());
                return _Inert_CONDPAIR(reducedCond, branch);
            end if;
        else
            EnvStack:-push(env:-clone());
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
# takes and returns an active representation
substitute := proc(active, env::bte)
    local eq, a;
    a := active;
    for eq in env:-list() do
        a := subs([convert(lhs(eq), name) = rhs(eq)], a);
    end do;
    return a;
end proc;


# takes and returns an inert representation
reduceBySubst := proc(stmt, env::bte) 
    ToInert(eval(substitute(FromInert(stmt), env)));
end proc;



# need a better reducer for boolean conditions
reduceCondition := proc(stmt, env::bte) 
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

env1 := BTE:-NewBTE(["x" = 5]);

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


env2 := BTE:-NewBTE(["x"=5, "y"=10]);
env3 := BTE:-NewBTE(["x"=5]);

p6 := proc(x, y, z)
    if x = y then
        return z;
    elif x > y then
        return x - y;
    else
        return y - x;
    end if;
end proc;
