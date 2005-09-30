# collection of functions for working with inert forms

# type of inert forms
`type/inert` := curry(funcPrefixType, '_Inert_');

# type used buy the partial evaluator's intermediate forms
`type/tag`   := curry(funcPrefixType, '_Tag_');


funcPrefixType := proc(prefix, f)
    if nargs = 2 then
        type(f, function) and StringTools:-RegMatch(cat("^", prefix), op(0, f));
    elif nargs = 3 then
        type(f, specfunc(anything, map2(cat, prefix, args[3])));
    else 
        error("must be called with 1 or 2 args");
    end if;
end proc;


isInert := proc(x) option inline;
    type(x, inert);
end proc:


# for extracting subexpressions from inert procedures
getParams   := proc(x) option inline; op(1,x) end proc:
getLocals   := proc(x) option inline; op(2,x) end proc:
getProcBody := proc(x) option inline; op(5,x) end proc:
getCond := proc(x) option inline; op(1,x) end proc:

# for extracting subexpressions from inert statments
getHeader := proc(x) option inline; op(0,x) end proc:
getVal := proc(x) option inline; op(1,x) end proc:
getParamName := proc(x) `if`(op(0,x)=_Inert_DCOLON, op(op(1,x)), op(x)) end proc:

isInertVariable := x -> member(getHeader(x), {_Inert_PARAM, _Inert_LOCAL}):


# Only flattens the outermost statment sequence, does not recurse into structures such as ifs and loops
flattenStatseq := proc(statseq::inert(STATSEQ))::inert(STATSEQ);
    local flatten;
    flatten := proc(inert)
        if getHeader(inert) = _Inert_STATSEQ then
            op(map(flatten, inert));
        else
            inert;
        end if;
    end proc;
    
    map(flatten, statseq);
end proc:


# returns true iff the given statment is a return or is a statseq that ends with a return
endsWithReturn := proc(inert::inert)
    if inert = _Inert_STATSEQ() then
        false;
    elif getHeader(inert) = _Inert_STATSEQ then
        procname(op(-1, flattenStatseq(inert)));
    else
        evalb(getHeader(inert) = _Inert_RETURN);
    end if;
end proc;


statmentForms := {_Inert_IF, _Inert_FORFROM, _Inert_FORIN, 
                  _Inert_BREAK, _Inert_NEXT, _Inert_RETURN, 
                  _Inert_ERROR, _Inert_TRY, _Inert_ASSIGN, 
                  _Inert_READ, _Inert_SAVE};


# expression forms that are supported so far
expressionForms := {_Inert_SUM, _Inert_PROD, _Inert_POWER, 
                    _Inert_CATENATE, _Inert_EQUATION, _Inert_LESSEQ, 
                    _Inert_LESSTHAN, _Inert_IMPLIES, _Inert_AND, 
                    _Inert_OR, _Inert_XOR, _Inert_NOT, 
                    _Inert_INTPOS, _Inert_INTNEG, _Inert_FLOAT, 
                    _Inert_STRING, _Inert_COMPLEX, _Inert_RATIONAL, 
                    _Inert_EXPSEQ, _Inert_LIST, _Inert_SET, 
                    _Inert_PARAM, _Inert_LOCAL, _Inert_NAME, 
                    _Inert_FUNCTION, _Inert_TABLEREF};
