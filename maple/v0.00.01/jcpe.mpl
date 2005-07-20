myPE := module()
	export pe, pe_test, reduce, analyse;
	global `index/defined`;
	local reduce_, evaluate, residualize, pe_main, 
	lookupvar,lub,analyseSEQ, reduceDAG, reducer,
	LazyReduce, LazyReduce2,
	addBindings, removeBindings,
	BindingTimes, # internal table of Binding Times
	BindingStack, # internal Stack of Binding Times for parameters and locals
	Value;       # internal table of NAME-Value bindings

####################################################################        

`index/defined` := proc(Idx::list,Tbl::table,Entry::list)
    if (nargs = 2) then
        if (assigned(Tbl[op(Idx)])) then 
		    Tbl[op(Idx)];
        else 
		    error "can not refer to unassigned entry";
        end if;
    else
        Tbl[op(Idx)] := op(Entry);
    end if;
end;

####################################################################        

# input is supposed to be in Maple form
pe := proc(e,bte::table)
    pe_main(ToInert(e), bte);
end;

# input is supposed to be in Inert form
pe_test := proc(e, bte)
    pe_main(e, bte);
end;

pe_main := proc(ee,bte)
    local bb, cc;
	if assigned(BindingTimes) then
	    error "this module is not re-entrant!";
	end if;
	try
		# makes it easier to debug
		BindingTimes := table('defined');
		BindingStack := SimpleStack();
		Value := table('defined');
		cc := analyse(ee, bte);
		bb := reduce(ee,cc,{});
	catch "case":
	    error;
	finally
		BindingTimes := 'BindingTimes';
		BindingStack := 'BindingStack';
		Value := 'Value';
		subsop(4=NULL, eval(lookupvar));
	end try;
	# the only way to actually get here is if the code above succeeded
	if cc=Stat then
		if type(bb,{'procedure','table'}) then eval(bb) else bb end if;
	else
		FromInert(bb);
    end if;
end proc;

reduce := proc(e::function,d,eqn::set)
	reduce_[eval(BindingTimes[e],eqn)](e,d);
end proc;        

reducer := table([Stat = (()->args), Dyn = ToInert]);

reduce_[Stat] := proc(e,d)
    local i,op1, res;

    i := op(0,e);
	if member(i, {_Inert_INTPOS, _Inert_INTNEG, _Inert_STRING,
	    _Inert_FLOAT, _Inert_RATIONAL, _Inert_COMPLEX}) then
        LazyReduce(e, reducer[d]);
    elif i = _Inert_NAME then
        reducer[d](lookupvar(op(1,e)));
    elif i = _Inert_ASSIGNEDNAME then
        reducer[d](lookupvar(op(1,e)));
	elif i = _Inert_EXPSEQ then
		op(reducer[d]([evaluate(reduceDAG(e,Stat))]));
	elif i = _Inert_PROC then
	    # First, install the proper bindings to BindingTimes
		addBindings(eval(BindingTimes[e, _Inert_PARAM]));
		# a STATSEQ must always be residualized
		op1 := reducer[Dyn](evaluate(reduceDAG(op(5,e),Stat)));
		removeBindings(eval(BindingTimes[e, _Inert_PARAM]));
		FromInert(subsop(5=_Inert_STATSEQ(op1), e));
	elif i = _Inert_IF then
	    # reduce one-by-one
		res := NULL;
		for op1 in e do
		    if op(0,op1)=_Inert_CONDPAIR then
				res := evaluate(reduceDAG(op(1,op1),Stat));
				if res=true then
				    return reducer[d](evaluate(reduceDAG(op(2,op1),Stat)));
				end if;
			else
				reducer[d](evaluate(reduceDAG(op1,Stat)));
			end if;
		end do;
	elif member(i, {_Inert_FUNCTION,
	    _Inert_STATSEQ, _Inert_CONDPAIR, 
        _Inert_SUM, _Inert_PROD, _Inert_POWER, 
		_Inert_LIST, _Inert_SET,
		_Inert_EQUATION, _Inert_INEQUAT, _Inert_LESSTHAN, _Inert_LESSEQ,
		_Inert_AND, _Inert_OR, _Inert_NOT, _Inert_XOR, _Inert_IMPLIES}) then
		reducer[d](evaluate(reduceDAG(e,Stat)));
	else
	    error "case of %1 not handled in Static yet", i;
    end if;
end proc;

# Tricky cases:
# _Inert_NAME: a Dynamic NAME is a symbol -- leave it be!
reduce_[Dyn] := proc(e,d)
    local i,op1,op2;
    i := op(0,e);
	if member(i, {_Inert_INTPOS, _Inert_INTNEG, _Inert_STRING,
	    _Inert_FLOAT, _Inert_RATIONAL}) then
    #      e;
	    error "these should never be Dynamic!";
	elif member(i, {_Inert_NAME}) then
	    e;
	elif member(i, {_Inert_IF, _Inert_EXPSEQ, _Inert_FUNCTION, _Inert_STATSEQ,
        _Inert_SUM, _Inert_PROD, _Inert_POWER, 
	    _Inert_CONDPAIR, _Inert_LIST, _Inert_SET,
		_Inert_EQUATION, _Inert_INEQUAT, _Inert_LESSTHAN, _Inert_LESSEQ,
		_Inert_AND, _Inert_OR, _Inert_NOT, _Inert_XOR, _Inert_IMPLIES}) then
        residualize(reduceDAG(e,d));
    elif member(i, {_Inert_SUM, _Inert_PROD, _Inert_POWER,
	    _Inert_EQUATION}) then
	    residualize(reduceDAG(e,d));
	elif i=_Inert_PROC then
		op1 := residualize(reduceDAG(op(5,e),Dyn));
		subsop(5=op1, e);
	else
		error "case of %1 not handled in Dynamic yet", i;
	end if;
end proc;

reduceDAG := proc(e,d,eq)
   op(0,e)(op(map(reduce,[op(e)],d,eq)));
end proc;

lookupvar := proc(v)
    option remember;
	try
	    Value[v];
	catch "can not refer to unassigned entry":
		if assigned(convert(v,'name')) then
			Value[v] := eval(convert(v,'name'));
		else
			error "Not found"
		end if;
	end try;
end proc;

addBindings := proc(t::table)
    local i;
    for i in map(op,[indices(t)]) do
	    BindingTimes[i] := t[i];
	od;
end proc;

removeBindings := proc(t::table)
    local i;
    for i in map(op,[indices(t)]) do
	    unassign(BindingTimes[i]);
	od;
end proc;

##################################################################

analyse := proc(e, bte)
   local op0, var, loc;
   op0 := op(0,e);
   if member(op0, {_Inert_INTPOS, _Inert_INTNEG, _Inert_STRING,
       _Inert_FLOAT, _Inert_RATIONAL}) then
	  BindingTimes[e] := Stat;
   elif member(op0, {_Inert_NAME}) then 
	  var := op(1,e);
	  if assigned(convert(var, 'name')) then
		  BindingTimes[e] := Stat;
	  else
		  BindingTimes[e] := bte[var];
	  end if;
   elif member(op0, {_Inert_ASSIGNEDNAME}) then 
	  BindingTimes[e] := Stat;
   elif member(op0, {_Inert_EQUATION, _Inert_CONDPAIR, _Inert_EXPSEQ,
		_Inert_STATSEQ, _Inert_SUM, _Inert_PROD,
		_Inert_IF, _Inert_COMPLEX, _Inert_POWER, _Inert_INEQUAT,
		_Inert_LESSEQ, _Inert_LESSTHAN, _Inert_AND, _Inert_OR,
		_Inert_NOT, _Inert_XOR, _Inert_IMPLIES,
		_Inert_LIST, _Inert_SET}) then
	   BindingTimes[e] := analyseSEQ(e,bte);
   elif op0 = _Inert_FUNCTION then 
       loc := analyse(op(1,e),bte);
	   rest := analyse(op(2,e),bte);
	   if member(rest, {Dyn,Stat}) then
	       if member(loc, {Dyn, Stat}) then
			   BindingTimes[e] := lub(loc,rest);
		   else
		       # arguments are known, match them up!
			   var := map2(op, 0, select(type, indets(loc), 'indexed'));
			   assert(nops(var)=1);
			   BindingTimes[e] := lub(rest,eval(loc, {seq(var[1][i]=BindingTimes[op([2,i],e)],i=1..nops(op(2,e)))}));
		   end if;
	   else
	       error "cannot tell!";
	   end if;
   elif op0 = _Inert_PROC then
       if not (op(2,e)=_Inert_LOCALSEQ() and
	           op(3,e)=_Inert_OPTIONSEQ() and
	           op(4,e)=_Inert_EXPSEQ() and
	           op(7,e)=_Inert_GLOBALSEQ() and
	           op(8,e)=_Inert_LEXICALSEQ()) then
           error "Procedure has unknown components";
		else
		    var := `tools/genglobal`(_YY);
		    BindingStack:-push(table('defined',
			    [seq(_Inert_PARAM(i)=var[i],i=1..nops(op(1,e)))]));
	        BindingTimes[e] := analyse(op(5,e),bte);
			loc := BindingStack:-pop();
			BindingTimes[e, _Inert_PARAM] := loc;
			BindingTimes[e]
		end if;
   elif op0 = _Inert_PARAM then
       BindingStack:-top()[e];
   else
	   error "Analysis of %1 not programmed yet", op0;
   end if;
end proc;

analyseSEQ := proc(e,bte)
	local l1;
	l1 := op(map(analyse,[op(e)],bte));
	BindingTimes[e] := foldl(lub,Stat,l1);
end proc;

lub := proc(t1,t2)
    if t1= Dyn then Dyn 
	elif t1=Stat then t2 
	elif t2=Stat then t1 
	else 'lub'(t1,t2) 
	end if;
end proc;

#################################################################

LazyReduce := proc(e,d) d(LazyReduce2(e)) end proc;

LazyReduce2 := proc(e)
    local op0;
	op0 := op(0,e);
    if op0 = _Inert_INTPOS then
	    op(1,e)
    elif op0 = _Inert_INTNEG then
	    -op(1,e)
    elif op0 = _Inert_RATIONAL then
	    procname(op(1,e)) / procname(op(2,e))
    elif op0 = _Inert_FLOAT then
	    Float(procname(op(1,e)),procname(op(2,e)))
    elif op0 = _Inert_STRING then
	    op(1,e);
	elif op0 = _Inert_COMPLEX then
	    if nops(e)=1 then
		    procname(op(1,e))*I
		else
		    procname(op(1,e))+procname(op(2,e))*I
		end if
	else
	    error "should not be here!";
	end if;
end proc;

evaluate := proc(e)
    local op0;

	op0 := op(0,e);
    if (op0 = _Inert_FUNCTION) then
	    op(1,e)(op(2..-1,e));
    elif (op0 = _Inert_SUM) then
		(`+`(op(e)));
    elif (op0 = _Inert_PROD) then
		(`*`(op(e)));
    elif (op0 = _Inert_POWER) then
		(`^`(op(e)));
    elif (op0 = _Inert_EXPSEQ) then
	    op(e)
    elif (op0 = _Inert_EQUATION) then
	    evalb(op(1,e) = op(2,e))
    elif (op0 = _Inert_INEQUAT) then
	    evalb(op(1,e) <> op(2,e))
    elif (op0 = _Inert_LESSTHAN) then
	    evalb(op(1,e) < op(2,e))
    elif (op0 = _Inert_LESSEQ) then
	    evalb(op(1,e) <= op(2,e))
    elif (op0 = _Inert_AND) then
	    evalb(op(1,e) and op(2,e))
    elif (op0 = _Inert_OR) then
	    evalb(op(1,e) or op(2,e))
    elif (op0 = _Inert_XOR) then
	    evalb(op(1,e) xor op(2,e))
    elif (op0 = _Inert_IMPLIES) then
	    evalb(op(1,e) implies op(2,e))
    elif (op0 = _Inert_NOT) then
	    evalb(not op(1,e))
    elif (op0 = _Inert_STATSEQ) then
	    # return the value of the last thing evaluated
	    op(-1,e);
	elif (op0 = _Inert_LIST) then
	    [op(e)]
	elif (op0 = _Inert_SET) then
	    {op(e)}
	else
		error "case %1 not evaluated yet", op(0,e);
	end if;
end proc;

residualize := proc(e) e end proc;

end module;
