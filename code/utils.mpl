# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.

printmod := proc(m)
    local printit, before, oper;
    before := kernelopts(opaquemodules=false);

    printit := proc(x)
        print(convert(x, string), x);
        print();
    end proc;

    if type(m, `module`) then

        # prints exports
        for oper in op(1, eval(m)) do
            printit(oper);
        end do;

        #prints locals
        for oper in op(3, eval(m)) do
            printit(oper);
        end do;
    else
        print(m);
    end if;

    kernelopts(opaquemodules=before);
    NULL;
end proc:
