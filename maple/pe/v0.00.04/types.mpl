
# 'type' for inert code

`type/inert` := proc(f)
    if nargs = 1 then
        type(f, function) and StringTools:-RegMatch("^_Inert_", op(0, f));
    elif nargs = 2 then
        type(f, specfunc(anything, map2(cat, '_Inert_', args[2])));
    else 
        error("must be called with 1 or 2 args");
    end if;
end proc;


# type equation
`type/equation` := anything=anything;
