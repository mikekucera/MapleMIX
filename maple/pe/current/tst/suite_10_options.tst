#test

# TEST SUITE 10: Options ################################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "E:\\School\\svn\\thesis\\maple\\pe\\current\\lib":

with(PEOptions);

#######################################################################


p := proc(x,y) x + y end proc;

sgoal := proc() p(4,5) end proc;
dgoal := proc(d) p(d,5) end proc;

ped := OnPE(sgoal);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 9 end proc);
Try(101, got, expected);

ped := OnPE(dgoal);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc(d) d + 5 end proc);
Try(102, got, expected);


opts := PEOptions():-addFunction(PURE,p);

ped := OnPE(sgoal, opts);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 9 end proc);
Try(103, got, expected);


ped := OnPE(dgoal, opts);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc(d) d + 5 end proc);
Try(104, got, expected);


opts := PEOptions():-addFunction(INTRINSIC,p);

ped := OnPE(sgoal, opts);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() 9 end proc);
Try(105, got, expected);

ped := OnPE(dgoal, opts);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc(d) p(d,5) end proc);
Try(106, got, expected);


opts := PEOptions():-addFunction(DYNAMIC,p);

ped := OnPE(sgoal, opts);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc() p(4, 5) end proc);
Try(107, got, expected);

ped := OnPE(dgoal, opts);
got := ToInert(eval(ped:-ModuleApply));
expected := ToInert(proc(d) p(d, 5) end proc);
Try(108, got, expected);

#######################################################################

#######################################################################

#end test