SmartOps := module()
    local
        handler; # table of special dynamic handlers
    export
        HasHandler, InvokeHandler;


    HasHandler := n -> assigned(handler[n]);

    InvokeHandler := proc(n::string, expseq::mform(ExpSeq)) local res;
        # will always be one argument because its dynamic
        ASSERT( assigned(handler[n]) );
        res := handler[n](expseq);
        if res = NULL then
            MFunction(MName(n), expseq);
        else
            res;
        end if;
    end proc;

    handler["nops"] := proc(expseq) local res, dyn;
        dyn := substop(op(expseq));
        if Header(dyn) = MList then
            nops(op(dyn))
        end if;
    end proc;

    handler["op"] := proc(expseq) local num, data, res;
        print();
        print("handler op", args);
        num := op(1, expseq);
        if num::MStatic('integer') then
            print("here1");
            num := op(num);
            print("num", op(num));

            data := substop(op(2, expseq));
            print("data", data);
            print("expr", nops(op(data)));

            if Header(data) = MList and num <= nops(op(data)) then

                print("here2");
                res := op(num, op(data));
                print("res", res);
                `if`(res::Static, op(res), res);
            end if;
        end if;
    end proc



end module:
