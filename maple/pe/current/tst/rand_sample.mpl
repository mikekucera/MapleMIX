kernelopts(opaquemodules=false):
libname := libname, "../lib":

opts := PEOptions();
opts:-setInlineAssigns();

test3:=proc(N,n)
   local i,a,X;
   use Statistics in
   X := RandomVariable(Normal(0,1)):
   for i from 1 to N do
       a:=Sample(X,n):
   end do:
   end use;
end proc:

res := OnPE(test3, opts);
got := eval(res:-ModuleApply);
