# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.


PETypes := module() option package;
    global `type/inert`, `type/mform`,
           `type/onenv`, `type/Static`, `type/Dynamic`, `type/Both`,
           `type/Global`, `type/Local`, `type/mname`, `type/envname`,
           `type/MStatic`, `type/PseudoStatic`;
    export ModuleLoad;
    local funcPrefixType;

# type of inert forms
`type/inert` := curry(funcPrefixType, '_Inert_'):

# type of M forms
`type/mform`     := curry(funcPrefixType, 'M'):

`type/Both`    := specfunc(anything, 'MBoth');
`type/Dynamic` := And('mform', 
                      Not(specfunc(anything, 'MStatic')), 
                      Not(specfunc(anything, 'MPseudoStatic')),
                      Not(Both)):
`type/Static`  := And(Not(Dynamic), Not(Both), Not(PseudoStatic));
`type/MStatic` := specfunc(anything, 'MStatic');
`type/PseudoStatic` := specfunc(anything, 'MPseudoStatic');

`type/Global` := 'Or'('identical'(MName), 'identical'(MAssignedName), 'identical'(MCatenate), mform({Name, AssignedName, Catenate})):
`type/Local`  := 'Or'('identical'(MLocal), 'identical'(MParam), 'identical'(MGeneratedName), 'identical'(MSingleUse), 'identical'(MLoopVar), mform({Local, GeneratedName, Param, SingleUse, LoopVar})):
`type/mname`  := 'Or(Global, Local)';
`type/envname`:= mform({Name, Local, GeneratedName, Param, SingleUse});

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
        error "type function must be called with 1 or 2 arguments, did you use forget to use {}";
    end if;
end proc:

end module:
