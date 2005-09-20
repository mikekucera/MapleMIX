# collection of functions for working with inert forms


# for extracting subexpressions from inert procedures
getParams   := proc(x) option inline; op(1,x) end proc;
getLocals   := proc(x) option inline; op(2,x) end proc;
getProcBody := proc(x) option inline; op(5,x) end proc;

getCond := proc(x) option inline; op(1,x) end proc;

# for extracting subexpressions from inert statments
getHeader := proc(x) option inline; op(0,x) end proc;
getVal := proc(x) option inline; op(1,x) end proc;
getParamName := proc(x) `if`(op(0,x)=_Inert_DCOLON, op(op(1,x)), op(x)) end proc;

isInertVariable := x -> member(getHeader(x), {_Inert_PARAM, _Inert_LOCAL});


isInert := proc(x) option inline;
    type(x, inert);
end proc:
