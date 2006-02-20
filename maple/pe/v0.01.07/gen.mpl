
NameGenerator := module()
    export ModuleApply;
    
    ModuleApply := proc(default::string := "x")
    	module()
    	    export ModuleApply, addSymbols;
    	    local vals, getVal, knownSymbols;   	    
    	    
    	    knownSymbols := {};
    	    
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
    	    
    	    ModuleApply := proc(prefix::string := default)
    	        newName := genName(prefix);
    	        while member(newName, knownSymbols) do
    	            newName := genName(prefix);
    	        end do;
    	        newName;
    	    end proc;
    	    	
    	end module;
    end proc;
    
end module: