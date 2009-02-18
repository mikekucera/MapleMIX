# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.

NameGenerator := module()
    export ModuleApply;
    
    ModuleApply := proc(default::string := "x")
    	module()
    	    export ModuleApply, addNames;
    	    local vals, knownSymbols,
    	          getVal, genName;   	    
    	    
    	    knownSymbols := {};
    	    vals := table();
    	    
    	    addNames := proc(newSymbols::set(string))
    	        knownSymbols := knownSymbols union newSymbols;
    	        NULL;
    	    end proc;
    	    
    	    getVal := proc(prefix)
    	        if assigned(vals[prefix]) then
    	            vals[prefix] := vals[prefix] + 1;
    	        else
    	            vals[prefix] := 1;
    	        end if;
    	    end proc;
    	    
    	    genName := proc(prefix)
    	        cat(prefix, getVal(prefix));
    	    end proc;
    	    
    	    ModuleApply := proc(prefix::string := default) # default is parameter to outer ModuleApply
    	        local newName;
    	        newName := genName(prefix);
    	        while member(newName, knownSymbols) do
    	            newName := genName(prefix);
    	        end do;
    	        newName;
    	    end proc;
    	    	
    	end module;
    end proc;
    
end module:
