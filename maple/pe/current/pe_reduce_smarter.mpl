SmartOps := module()
    local
        handler; # table of special dynamic handlers
    export
        HasHandler, InvokeHandler;


    HasHandler := n -> assigned(handler[n]);

    InvokeHandler := proc(n::string, arg::mform(ExpSeq)) local res;
        # will always be one argument because its dynamic
        ASSERT( assigned(handler[n]) );
        res := handler[n](arg);
        if res = NULL then
            MFunction(MName(n), arg);
        else
            res;
        end if;
    end proc;

    handler["nops"] := proc(arg) local res, dyn;
        dyn := op(arg);
        if Header(dyn) = MList then
            nops(op(dyn))
        end if;
    end proc;





end module:
