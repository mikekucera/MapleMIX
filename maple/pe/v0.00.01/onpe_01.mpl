
# Simple online partial evaluator for a subset of maple
# Only works on simple expressions


OnPE := module()
    description "simple online partial evaluator for a subset of Maple";
    export pe, makeGenerator;
    local pe_main, tblToList, replace,
          isDynamic, isStatic, isVal,
          reduceExpr, reduceExprInert, reduceCondition,
          reduceStmt, reduceIf, subsVars, isTrue, isFalse,
          getParams, getLocals, getProcBody, getHeader, getVal, getCondition,
          EnvStack, combineEnvs,
          gen;


##################################################################################


# returns a closure that generates unique names (as strings);
makeGenerator := proc() 
    local val;
    val := 0;
    return proc()
        val := val + 1;
        "x_" || val;
    end proc;
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



pe := proc(p::procedure, env::bte)
    local inert, body, params, locals,
          newParamList, newLocalList;

    gen := makeGenerator();

    EnvStack := SimpleStack();
    EnvStack:-push(env:-clone());

    # get the inert form of the procedure
    inert := ToInert(eval(p));

    params := getParams(inert);
    locals := getLocals(inert);
    body   := getProcBody(inert);

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


isDynamic := x -> EvalExp:-isInert(x);
isStatic  := x -> not isDynamic(x);

isVal := proc(e) 
    member(e, {_Inert_INTPOS, _Inert_INTNEG, _Inert_STRING, _Inert_FLOAT, _Inert_RATIONAL});
end proc;

# only supports assignemnts and some returns
reduceStmt := proc(stmt) 
    local reduced, header, env;

    header := getHeader(stmt);
    env := EnvStack:-top();

    if isVal(header) then # implicit return of a value
        stmt;
    
    elif typematch(stmt, _Inert_RETURN('e'::anything)) then
        reduced := reduceExprInert(e, env);
        _Inert_RETURN(reduced);

    elif typematch(stmt, _Inert_NAME('n'::string)) then
        if env:-dynamic?(n) then stmt;
        else ToInert(env:-get(n));
        end if;

    elif header = _Inert_IF then
        reduceIf(stmt);

    elif typematch(stmt, _Inert_ASSIGN(_Inert_NAME('n'::string), 'e'::anything)) then
        reduced := reduceExpr(e, env);
        if isStatic(reduced) then
            env:-put(n, reduced);
            NULL;
        else
            env:-setDynamic(n);
            _Inert_ASSIGN(_Inert_NAME(n), reduced);
        end if;
    else
        error cat("not supported yet: ", stmt);
    end if;
end proc;


getCondition := proc(x) option inline; op(1,x); end proc;


reduceExpr := proc(x, env)
    option inline;
    EvalExp:-reduce(x, env);
end proc;

reduceExprInert := proc(x, env)
    local red;
    red := reduceExpr(x, env);
    `if`(isDynamic(red), red, ToInert(red));
end proc;


reduceIf := proc(stmt) 
    local red, env, coll, reducedIf, finished;

    finished := false;
    env := EnvStack:-top();
    coll := SimpleStack();

    red := proc(s) local branch, reducedCond;
        if finished then return NULL end if;

        if getHeader(s) = _Inert_CONDPAIR then
            reducedCond := reduceCondition(getCondition(s), env); # reduce the condition
    
            if isDynamic(reducedCond) then
                #generate a condpair
                EnvStack:-push(env:-clone());
                branch := map(reduceStmt, op(2, s));                
                coll:-push(EnvStack:-pop());
                _Inert_CONDPAIR(reducedCond, branch);                
                
            elif reducedCond then
                finished := true; #stop processing other branches
                EnvStack:-push(env:-clone());                
                branch := map(reduceStmt, op(2, s));
                coll:-push(EnvStack:-pop());
                return branch;                
                
            else
                return NULL;
            end if;
        else
            EnvStack:-push(env:-clone());
            branch := map(reduceStmt, s);
            coll:-push(EnvStack:-pop());
            branch;
        end if;
    end proc;

    reducedIf := map(red, stmt);

    EnvStack:-pop();
    EnvStack:-push(combineEnvs(coll));
    

    # collect environments and alter as neccessary

    if reducedIf = _Inert_IF() then
        NULL;
    elif not op(0, op(1, reducedIf)) = _Inert_CONDPAIR then #strip away unneccesary inertif
        op(1, reducedIf);
    else
        reducedIf;
    end if;
end proc;



combineEnvs := proc(stack::Stack) 
    local z;
    z := stack:-pop();
    while not stack:-empty() do
        z := z:-combine(stack:-pop());
    end do;
    z;
end proc;


reduceCondition := proc(e, env::bte) 
    evalb(reduceExpr(e, env));    
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


p7 := proc(a, b, c, d, s)
    if a = b then
        s := 5;
        return s*Pi;
    elif a > b then
        if a=1 then
            99;
        else
            40;
        end if;
    else
        s := 5;
    end if;
    
    return s * 10;
end proc;

env4 := BTE:-NewBTE(["a"=1, "c"=5]);
