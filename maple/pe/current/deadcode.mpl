# This file is part of MapleMIX, and licensed under the BSD license.
# Copyright (c) 2007, Jacques Carette and Michael Kucera
# All rights reserved.  See file COPYING for details.

CodeCleanup := module()
    export
        RemoveDeadCodeSimple, InlineAssignsSimple;
    local
$include "access_header.mpl"
nothing;
$include "access.mpl"


    RemoveDeadCodeSimple := module()
        export 
            ModuleApply;
        local
            simpleAlg, cpair, findNames, simpleAlgLoop, hasName;
        
        ModuleApply := proc(p) local m, _;
            if type(p, 'procedure') then
                m, _ := M:-ToM(ToInert(eval(p)));
                simpleAlg(m):-code;
            elif type(p, mform) then
                simpleAlg(p):-code;
            else
                error "argument must be of type procedure or mform, got %1", p;
            end if;
        end proc;
    
    
        simpleAlg := proc(m::mform, ns::set := {}, {loop := false})
            local h, names, q, n, c, t, e, i, x, res, res1, res2, hasN;
    
            names := ns;
            h := Header(m);
            #print("simpleAlg", h, names);
    
            # case analysis on the statment type
            if h = MProc then
                res := procname(op(5, m), names);
                cpair(res:-names, subsop(5 = res:-code, m));
    
            elif h = MStatSeq then
                q := SimpleQueue();
                for i from 1 to nops(m) do
                    res := procname(op(-i, m), names);
                    if res:-code <> NULL then
                        q:-enqueue(res:-code);
                    end if;
                    #print("names", names);
                    names := names union res:-names;
                    #print("names2", names);
                end do;
                cpair(names, MStatSeq(op(ListTools:-Reverse(q:-toList()))))
    
            elif member(h, {MStandaloneExpr, MStandaloneFunction, MReturn, MError}) then
                cpair(findNames(m), m);
    
            elif typematch(m, MAssign('n'::mname, 'e'::mform))
            or   typematch(m, MAssignToTable('n'::mname, 'e'::mform))
            or   typematch(m, MAssignToFunction('n'::mname, 'e'::mform)) then
                names := names union `if`(loop, {n}, {});
                if not hasName(n, names) then
                    cpair(names, NULL);
                else
                    cpair(names union findNames(e), m);
                end if;
    
            elif typematch(m, MAssign('n'::mform(ExpSeq), 'e'::mform)) then
            	hasN := ormap(x -> hasName(x,names), n);
            	
            	for x in n do
	            	names := names union `if`(loop, {x}, {});
	            end do;
            	
	            if hasN then
	            	cpair(names union findNames(e), m);
	            else
	                cpair(names, NULL);
	            end if;
            
            elif typematch(m, MAssignTableIndex(MTableref('n'::mname, 'c'::mform), 'e'::anything)) then
                names := names union `if`(loop, {n}, {});
                if not hasName(n, names) then
                    cpair(names, NULL);
                else
                    cpair(names union findNames(e) union findNames(c), m);
                end if;
    
    
            elif typematch(m, MIfThenElse('c'::mform, 't'::mform, 'e'::mform)) then
                #print("MIfThenElse", c, t, e);
                res1 := procname(t, names);
                res2 := procname(e, names);
                cpair(res1:-names union res2:-names union findNames(c),
                      MIfThenElse(c, res1:-code, res2:-code));
    
            elif h = MCommand then
                cpair(names, NULL);
    
            elif h = MWhile then #loops
                simpleAlgLoop(m, names, 4)
    
            elif h = MWhileForFrom then
                simpleAlgLoop(m, names, 5)
    
            elif h = MWhileForIn then
                simpleAlgLoop(m, names, 3)
    
            else
                error "Unknown syntactic form %1", m; #cpair({}, m)
            end if
        end proc;
    
        hasName := (n, names) -> member(`if`(n::Local, MLocal(op(1,n)), n), names);
    
    
        simpleAlgLoop := proc(m, ns, num) local names, res;
            #print("simpleLoopAlg");
            names := ns;
            # first time is just to gather names
            res := simpleAlg(op(-1,m), names, loop=true);
            #print("sla", res:-names, names);
            res := simpleAlg(op(-1,m), names union res:-names); # for real this time
            names := names union foldl(`union`, op(map(findNames, [op(1..num, m)])));
            cpair(res:-names union names, subsop(-1 = res:-code, m));
        end proc;
    
    
        findNames := proc(e::mform) local names, found;
            #print("findNames", args);
            names := table();
            found := f -> proc(n)
                              names[f(n)] := 'blah';
                          end proc;
    
            eval(e, [MLocal = found(MLocal),
                     MParam = found(MLocal),
                     MSingleUse = found(MLocal),
                     MGeneratedName = found(MLocal),
                     MLexicalLocal = found(MLexicalLocal),
                     MLocalName = found(MLocalName),
                     MAssignedLocalName = found(MAssignedLocalName),
                     MName = found(MName),
                     MAssignedName = found(MAssignedName)
            ]);
    
            #print("what", indices(names));
    
            {op(map(op, [indices(names)]))};
        end proc;
    
        cpair := proc(n::set, c)
            if nargs = 1 then
                Record('code'=NULL, 'names'=n);
            else
                Record('code'=c, 'names'=n);
            end if;
        end proc;
    end module;
    
    
    InlineAssignsSimple := module()
        export
            ModuleApply;
        local
            readCount, writeCount,
            substit, shouldInline,
            countExpr, countStmt, addToCount, count, 
            cleanStmt, cleanExpr, clean;
        
        # Supports the following statements
        # MAssign, MAssignTableIndex, MIfThenElse, MStandaloneExpr
        
        ModuleApply := proc(p::mform(Proc)) local res;
        
            readCount  := table();
            writeCount := table();
        
            countStmt(ProcBody(p));
            
            substit := table();
            
            res := subsop(5 = cleanStmt(ProcBody(p)), p);
            
            readCount  := 'readCount';
            writeCount := 'writeCount';
            substit := 'substit';
            res; 
        end proc;
        
        
        # supports the following names: MLocal, MTableRef
        countExpr := proc(expr) local countLocal, countTableref;        
            countLocal := f -> proc(n)
                addToCount(readCount, f(n));
                f(n);
            end proc;
            countTableref := proc(n, i)
                addToCount(readCount, MTableref(n,i));
                MTableref(n,i);
            end proc;
            eval(expr, [MLocal=countLocal(MLocal), 
                        MGeneratedName=countLocal(MGeneratedName), 
                        MTableref=countTableref]);
            NULL; 
        end proc;
        
        countStmt := proc(stmt) local h;
            h := Header(stmt);
            if assigned(count[h]) then
                count[h](op(stmt));
            else
                error "statement form not supported %1", h;
            end if;
            NULL; 
        end proc;
        
        addToCount := proc(tbl, index)
            tbl[index] := `if`(assigned(tbl[index]), tbl[index] + 1, 1);
            NULL; 
        end proc;
        
        count[MAssign] := proc(n, e)
            addToCount(writeCount, n);
            countExpr(e);
            NULL; 
        end proc;
        
        count[MAssignTableIndex] := proc(tr, e)
            addToCount(writeCount, tr);
            countExpr(e);
            NULL; 
        end proc;
        
        count[MStandaloneExpr] := proc(e)
            countExpr(e);
            NULL; 
        end proc;
        
        count[MIfThenElse] := proc(c, t, e)
            countExpr(c);
            countStmt(t);
            countStmt(e);
            NULL; 
        end proc;
        
        count[MError] := proc(e)
            countExpr(e);
            NULL;
        end proc;

        count[MStatSeq] := proc()
            map(countStmt, [args]);
            NULL; 
        end proc;
        
        
        ########################################################
        
        
        shouldInline := proc(n)
            assigned(readCount[n]) and 
            readCount[n] = 1 and
            assigned(writeCount[n]) and
            writeCount[n] = 1
        end proc;
        
        cleanExpr := proc(expr) local tryInline;
            tryInline := f -> proc()
                if assigned(substit[f(args)]) then
                    substit[f(args)];
                else
                    f(args);
                end if;
            end proc;
            
            eval(expr, [MLocal=tryInline(MLocal), 
                        MGeneratedName=tryInline(MGeneratedName),
                        MTableref=tryInline(MTableref)]);        
        end proc;
        
        cleanStmt := proc(stmt) local h;
            h := Header(stmt);
            if assigned(clean[h]) then
                clean[h](op(stmt));
            else
                error "statement form not supported %1", h;
            end if;
        end proc;
        
        clean[MAssign] := proc(n, e)
            if shouldInline(n) then
                substit[n] := e;
                NULL;
            else
                MAssign(n, cleanExpr(e));
            end if;
        end proc;
        
        clean[MAssignTableIndex] := proc(tr, e)
            if shouldInline(tr) then
                substit[tr] := e;
                NULL;
            else
                MAssignTableIndex(tr, cleanExpr(e));
            end if;
        end proc;
        
        clean[MStandaloneExpr] := proc(e)
            MStandaloneExpr(cleanExpr(e));
        end proc;
        
        clean[MIfThenElse] := proc(c, t, e)
            MIfThenElse(cleanExpr(c), cleanStmt(t), cleanStmt(e));
        end proc;
        
        clean[MStatSeq] := proc()
            MStatSeq(op(map(cleanStmt, [args])));
        end proc;
        
        clean[MError] := proc(e)
            MError(cleanExpr(e));
        end proc;
            
    end module;
    
    
end module:


