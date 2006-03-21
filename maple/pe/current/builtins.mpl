Builtins := module() option package;
    local
        numToName, builtinNames;
    export
        getName, isBuiltin, getNum;

    builtinNames := {anames(builtin)};
    numToName := table(map(x -> op([5,1,1], ToInert(eval(x))) = x, builtinNames));

    getName := proc(x::Or(procedure,posint))
        if x::posint then
            ASSERT(assigned(numToName[num]), "invalid builtin number");
            numToName[num];
        else
            numToName[getNum(x)];
        end if
    end proc;

    isBuiltin := proc(p::procedure)
        evalb(op(3,eval(p)) = 'builtin');
    end proc;

    getNum := proc(p::procedure)
        ASSERT(isBuiltin(p), "procedure must be builtin");
        op([5,1,1], ToInert(eval(p)));
    end proc;

end module:
