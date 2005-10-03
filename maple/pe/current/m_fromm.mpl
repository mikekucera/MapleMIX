
FromM := module()
    export ModuleApply;
    local i, mtoi, mtoi2, mapmtoi;

    i := table();
    mtoi, mtoi2, mapmtoi := transformProcs(i);

    ModuleApply := proc(code::m)
        eval(FromInert(mtoi(code)));
    end proc;

    i[MName] := _Inert_NAME;
    i[MLocal] := _Inert_LOCAL;
    i[MParam] := _Inert_PARAM;

    i[MInt] := x -> `if`(x < 0, _Inert_INTNEG, _Inert_INTPOS)(abs(x));
    i[MString] := _Inert_STRING;
    
    i[MNot] := _Inert_NOT @ mtoi;


end module;
