
NameGenerator := module()
    export ModuleApply;
    
    ModuleApply := proc(default::string := "x")
    	module()
    	    export ModuleApply;
    	    local vals, getVal;   	    
    	    
    	    getVal := proc(prefix)
    	        if assigned(vals[prefix]) then
    	            vals[prefix] := vals[prefix] + 1;
    	        else
    	            vals[prefix] := 1;
    	        end if;
    	    end proc;
    	    
    	    ModuleApply := proc(prefix::string := default)
    	        cat(prefix, getVal(prefix))
    	    end proc;
    	    	
    	end module;
    end proc;
    
end module: