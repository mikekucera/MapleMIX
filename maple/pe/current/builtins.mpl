Builtins := module() option package;
    local
        numToName, builtinNames, operators;
    export
        getName, isBuiltin, getNum, isOperator, getOperatorAsM;

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
    
    isOperator := proc(n::procedure)
        isBuiltin(n) and assigned(operators[getNum(n)]);
    end proc;
    
    getOperatorAsM := proc(n::procedure)
        ASSERT(isOperator(n), "not an operator");
        operators[getNum(n)];
    end proc;

    # TODO finish this list
    operators[getNum(`<=`)] := MLesseq;
    operators[getNum(`<`)]  := MLessThan;
    operators[getNum(`>`)]  := (x,y) -> MLessThan(y,x);
    operators[getNum(`>=`)] := (x,y) -> MLesseq(y,x);
    operators[getNum(`=`)]  := MEquation;
    operators[getNum(`<>`)] := MInequat;
    operators[getNum(`+`)]  := MSum;
    operators[getNum(`*`)]  := MProd;
    
end module:
