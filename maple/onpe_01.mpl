# Simple online partial evaluator for a subset of maple
# Only works on simple expressions


OnPE := module()
    export pe, reduceBody, isVal;
    global `index/dyn`;
    local onEnv, tblToList, varMap, replace, substitute;

##################################################################################


`index/dyn` := proc(Idx::list, Tbl::table, Entry::list)
    local op1;
    if nargs = 2 then
        if assigned(Tbl[op(Idx)]) then
            Tbl[op(Idx)];
        else
            Dyn;
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
    local inert, var, counter, code;

    if not whattype(eval(p)) = procedure then
        error "Currently on partial evaluation of single procedures is supported";
    elif not op(op(1,env)) = dyn then
        error "Only index/dyn tables allowed!";
    end if;

    onEnv := env;
    inert := ToInert(eval(p));

    varMap := table();

    counter := 1;
    for var in op(1, inert) do
        varMap[_Inert_PARAM(counter)] := var;
        counter := counter + 1;
    end do;

    counter := 1;
    for var in op(2, inert) do
        varMap[_Inert_LOCAL(counter)] := var;
        counter := counter + 1;
    end do;

    code := reduceBody(op(5,inert));
    onEnv := 'onEnv';

    print("done");
    for var in code do
        print(FromInert(var));
    end do;

end proc;



reduceBody := proc(stmtSeq) 
    local params, locals,
          head, stmt, code, reduced, val;

    code := [];

    for stmt in stmtSeq do
        stmt := replace(stmt);
        head := op(0, stmt);

        if isVal(head) then # implicit return of a value
            code := [op(code), stmt];
        elif head = _Inert_NAME then # implicit return of a name
            print("implicit return of a name");
            val := onEnv[op(1, stmt)];
            if val = Dyn then
                code := [op(code), stmt];
            else
                print(val);
                code := [op(code), ToInert(val)];
            end if;
        elif head = _Inert_ASSIGN then         
            print("assignment statment");   
            reduced := substitute(op(2, stmt));
            print(reduced);
            if isVal(reduced) then
                print("its a val");
                onEnv[op(1,op(1,stmt))] := op(1, reduced);
                print(onEnv);
            else
                print("its not a val");
                code := [op(code), _Inert_ASSIGN(op(1,stmt), reduced)];
                onEnv[op(1,op(1,stmt))] := Dyn
            end if;
        end if;
    end do;

    code;
end proc;



# replaces references to locals and parameters with their names
replace := proc(stmt) 
    subs(tblToList(varMap, 1), stmt);
end proc;


# replaces variables by their static values then simplifies
substitute := proc(stmt) 
    local i, active;
    active := FromInert(stmt);
    for i in indices(onEnv) do
        print([convert(i[1],name) = onEnv[i[1]]]);
        active := subs([convert(i[1],name) = onEnv[i[1]]], active);
    end do;
    ToInert(active);
end proc;


isVal := proc(e) 
    member(op(0, e), {_Inert_INTPOS, _Inert_INTNEG, _Inert_STRING, _Inert_Float, _Inert_RATIONAL});
end proc;

# converts a table into a list of equations
tblToList := proc(tbl, subs) 
    op(op(tbl))[subs];
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