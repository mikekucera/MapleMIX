
PETypes := module() option package;
    global `type/inert`, `type/mform`,
           `type/onenv`, `type/Static`, `type/Dynamic`;
    export ModuleLoad;

# type of inert forms
`type/inert` := curry(funcPrefixType, '_Inert_'):

# type of M forms
`type/mform`     := curry(funcPrefixType, 'M'):

`type/onenv` := '`module`'('putVal', 'getVal'):

`type/Static`  := 'Not'('mform'):
`type/Dynamic` := 'mform':



ModuleLoad := proc()
    protect('mform');
end proc;


funcPrefixType := proc(prefix, f)
    if nargs = 2 then
        try
            type(f, function) and StringTools:-RegMatch(cat("^", prefix), op(0, f));
        catch:
            return false;
        end try;
    elif nargs = 3 then
        type(f, specfunc(anything, map2(cat, prefix, args[3])));
    else
        error "type function must be called with 1 or 2 arguments";
    end if;
end proc:


# tables that throw exceptions if you try to look up a key that doesn't exist
`index/err` := proc(Idx::list,Tbl::table,Entry::list)
    if (nargs = 2) then
        if (assigned(Tbl[op(Idx)])) then
            eval(Tbl[op(Idx)]);
        else
            error "no mapping for: %1", op(Idx);
        end if;
    else
        Tbl[op(Idx)] := op(Entry);
    end if;
end proc:

# debugging table, prints out the key on every lookup
`index/deb` := proc(Idx::list,Tbl::table,Entry::list)
    if (nargs = 2) then
        print("lookup: ", op(Idx));
        eval(Tbl[op(Idx)]);
    else
        Tbl[op(Idx)] := op(Entry);
    end if;
end proc:

end module:
