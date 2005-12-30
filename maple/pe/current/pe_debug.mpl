PEDebug := module()
    export Begin, Statement, FunctionCall,
           DisplayReduceStart, DisplayReduceEnd, DisplayStatmentStart, DisplayStatmentEnd;
    local runningMode, quitIt, SetRunningMode, Quit, 
          x, y, displayStats, displayReductions,
          STEP, FUNCTION_CALL, FUNCTION_RETURN, COMPLETION;    
    use Maplets[Elements], Maplets[Tools] in
        
    
    runningMode := COMPLETION;
    quitIt := false;
    x, y := 10, 10;
    displayStats, displayReductions := false, false;
    stackSize := 0;
    
    
    SetRunningMode := proc(mode)
    	runningMode := mode;
    end proc;
    
    
    RememberVals := proc()
        x := Get('W1'('xcoord'));
        y := Get('W1'('ycoord'));
        displayStats := Get('C1'('value'));
        displayReductions := Get('C2'('value'));
    end proc;
    
    
    Begin := proc(stmt)
        displayStats, displayReductions := true, true;
        SetRunningMode(STEP);
        DisplayDebugCommand("Starting");
    end proc;
    
    Quit := proc()
        displayStats, displayReductions := false, false;
        quitIt := true;
    end proc;
    
    DisplayReduceStart := proc(r)
        if not runningMode = FUNCTION_RETURN and displayReductions then
            print("reducing: ", r);            
        end if;
    end proc;
    
    DisplayReduceEnd := proc(r)
        if not runningMode = FUNCTION_RETURN and displayReductions then
            if nargs = 0 then
                print("reduced: null");
            else
                print("reduced: ", r);
            end if;
        end if;
    end proc;
    

    StatementStart := proc(stmt)
        if not runningMode = FUNCTION_RETURN and displayStats then
            print(stmt);
        end if;
        if runningMode = STEP then
            DisplayDebugCommand(Header(stmt));
        end if;
    end proc;
    
    
    StatementEnd := proc(stat)
        if runningMode = STEP and displayStats then
            if nargs = 0 then
                print("null");
            else
                print(stat);
            end if;
            print();
        end if;
    end proc;
    
    
    FunctionStart := proc(n)
        if runningMode = FUNCTION_RETURN then
            stackSize := stackSize + 1;
        elif member(runningMode, {STEP, FUNCTION_CALL}) then
            print("Function Call: ", n);
            DisplayDebugCommand("Call", true);
        end if;
    end proc;    
    
    FunctionEnd := proc()
        if runningMode = FUNCTION_RETURN then
            if stackSize = 0 then
                SetRunningMode(STEP);
            else
                stackSize := stackSize - 1;
            end if;
        end if;
    end proc;
    
    DisplayEnv := proc()
        print("local env");
        callStack:-topEnv():-display();
        print("global env");
        genv:-display();
    end proc;
    
    DisplayDebugCommand := proc(message := "", skippable := false)
        use buttonWidth = 160, 
            A1 = Action(Evaluate(function = 'RememberVals()'), CloseWindow('W1')) 
        in
	    maplet := Maplet( 'onstartup' = RunWindow('W1'),
	        Window['W1']( 'title'= "PE Debug", 'xcoord' = x, 'ycoord' = y, [
	            Label(convert(message, string), 'font' = Font("courier", 18)),
	            " ",
	            Button['B1']("Step", 'width' = buttonWidth,
	                         Action(A1)),
	            Button['B2']("Skip Over Function", 'width' = buttonWidth, 'enabled' = skippable,
	                         Action(Evaluate(function = 'SetRunningMode(FUNCTION_RETURN)'), A1)),
	            Button['B3']("Run to Function Call", 'width' = buttonWidth,
	                         Action(Evaluate(function = 'SetRunningMode(FUNCTION_CALL)'), A1)),
	            Button['B4']("Run to Completion", 'width' = buttonWidth, 
	                         Action(Evaluate(function = 'SetRunningMode(COMPLETION)'), A1)),
	            Button['B5']("Quit", 'width' = buttonWidth,
	                         Action(Evaluate(function = 'Quit()'), A1)),
	            " ",
	            Button['B6']("Display Env", 'width' = buttonWidth,
	                         Evaluate(function = 'DisplayEnv()')),
	            " ",
	            CheckBox['C1']('caption' = "Display Statements", 'value' = displayStats),
	            CheckBox['C2']('caption' = "Display Reductions", 'value' = displayReductions)
	        ])
	    );
	    end use;
        Maplets:-Display(maplet);
        if quitIt then
            error "debug session exited";
        end if;
    end proc;

    end use;    
end module;