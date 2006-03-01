PEDebug := module()
    export Begin, RunThenStop, Statement, FunctionCall,
           DisplayReduceStart, DisplayReduceEnd, 
           DisplayStatmentStart, DisplayStatmentEnd,
           StepUntil, GetStatementCount, Message,
           RememberVals, DisplayEnv, DisplayVar,
           StatementStart, StatementEnd,
           FunctionStart, FunctionEnd;
    local DisplayDebugCommand,
          runningMode, quitIt, SetRunningMode, Quit, 
          x, y, displayStats, displayReductions,
          stackSize, statementCount, runThenStop, stepUntil,
          STEP, # run to next statment, or run given number of statments
          FUNCTION_CALL, # run to next function call
          FUNCTION_RETURN, # skip over a function
          COMPLETION; # run all the way to the end
    use Maplets[Elements], Maplets[Tools] in
        
    
    runningMode := COMPLETION;
    quitIt := false;
    x, y := 10, 10;
    displayStats, displayReductions := false, false;
    
    stackSize := 0; # used to skip over function calls
    statementCount := 0; # number of statements that have been run so far
    runThenStop := false;
    stepUntil := 'stepUntil'; # used to run the PE until a given statment number
    
    
    SetRunningMode := proc(mode)
    	runningMode := mode;
    end proc;
    
    
    RememberVals := proc()
        x := Get('W1'('xcoord'));
        y := Get('W1'('ycoord'));
        displayStats := Get('C1'('value'));
        displayReductions := Get('C2'('value'));
    end proc;
    
    
    GetStatementCount := () -> statementCount;
    
    Begin := proc(stmt)
        displayStats, displayReductions := true, true;
        statementCount := 0;
        stepUntil := 'stepUntil';
        SetRunningMode(STEP);
        DisplayDebugCommand("Starting");
    end proc;
    
    RunThenStop := proc(num::nonnegative)
        displayStats, displayReductions := true, true;
        statementCount := 0;
        StepUntil(num);
        runThenStop := true;
    end proc;
    
    StepUntil := proc(num::nonnegative)
        stepUntil := num;
        SetRunningMode(STEP);
    end proc;
    
    DisplayVar := proc(varName)
        print(eval(callStack:-topEnv():-getVal(convert(varName, string))));
    end proc;

    Quit := proc()
        displayStats, displayReductions := false, false;
        quitIt := true;
    end proc;
    
    DisplayReduceStart := proc(r)
        if runningMode <> FUNCTION_RETURN and displayReductions then
            print("reducing: ", r);            
        end if;
    end proc;
    
    DisplayReduceEnd := proc(r)
        if runningMode <> FUNCTION_RETURN and displayReductions then
            print("reduced:", `if`(nargs=0, "null", r));
        end if;
    end proc;
    
    DisplayEnv := proc()
        print("local env");
        callStack:-topEnv():-display();
        print("global env");
        genv:-display();
        print();
    end proc;
    
    
    # following functions are 'hooks' that are called in key places in the PE
    
    StatementStart := proc(stmt)
        if runThenStop and statementCount >= stepUntil then
            error "debug session exited";
        end if;    
        statementCount := statementCount + 1;
        if runningMode <> FUNCTION_RETURN and displayStats then
            print();
            if Header(stmt) = MIfThenElse then
                print("statement start: ", MIfThenElse(Cond(stmt)));
            else
                print("statement start:", stmt);
            end if;
        end if;
        if runningMode = STEP and not runThenStop then
            DisplayDebugCommand(Header(stmt));
        end if;
    end proc;
    
    Message := proc(msg)
        if displayStats and runningMode <> FUNCTION_RETURN then
            print(msg)
        end if
    end proc;
    
    StatementEnd := proc(stat)
        if displayStats and runningMode <> FUNCTION_RETURN then
            print("statement output:", `if`(nargs=0, "null", stat));
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
    
    
    # displays the debug mini-gui
    
    DisplayDebugCommand := proc(message := "", skippable := false) local maplet;
        if runThenStop or (assigned(stepUntil) and stepUntil > statementCount) then 
            return 
        end if;
        
        use buttonWidth = 160, 
            A1 = Action(Evaluate(function = 'RememberVals()'), CloseWindow('W1')) 
        in
	    maplet := Maplet( 'onstartup' = RunWindow('W1'),
	        Window['W1']( 'title'= "PE Debug", 'xcoord' = x, 'ycoord' = y, [
	            Label(convert(message, string), 'font' = Font("courier", 18)),
	            convert(statementCount, string),
	            " ",
	            Button['B1']("Step", 'width' = buttonWidth,
	                         Action(A1)),
	            [
	                Button['B7']("Step Until", 'width' = buttonWidth - 40, 
	                              Action(Evaluate(function = 'StepUntil(T1)'), A1)),
	                TextField['T1'](3)
	            ],
	            " ",              
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
	            [
	                Button['B8']("Display Var", 'width' = buttonWidth - 40, 
	                              Action(Evaluate(function = 'DisplayVar(T2)'))),
	                TextField['T2'](3)
	            ],
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
        NULL;
    end proc;

    end use;    
end module;