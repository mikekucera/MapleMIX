#test

# TEST SUITE : Multiple Assignment #######################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "../lib":


# TEST 1 ##############################################################

goal := proc(a) local x, y;
   	x, y := 1, a;
   	x, y;
end proc:

optimized := proc(a) local y;
	y := a;
	1, y;
end proc:

ped := OnPE(goal):

got := ToInert(eval(ped[ModuleApply])):
expected := ToInert(eval(optimized)):


Try(100, got, expected);


# TEST 2 ##############################################################


goal := proc(x, y) local a,b,c,d;
   	a, b, c, d:= 1, x, 2, y;
   	[a,b,c,d];
end proc:

optimized := proc(x, y) local b,d;
	b := x;
	d := y;
	[1,b,2,d];
end proc:

ped := OnPE(goal):

got := ToInert(eval(ped[ModuleApply])):
expected := ToInert(eval(optimized)):


Try(200, got, expected);


# TEST 3 ##############################################################
# all static

goal := proc() local a,b,c,d;
   	a, b, c, d:= 1,2,3,4;
   	[d,c,b,a];
end proc:

optimized := proc()
	[4,3,2,1];
end proc:

ped := OnPE(goal):

got := ToInert(eval(ped[ModuleApply])):
expected := ToInert(eval(optimized)):


Try(300, got, expected);


# TEST 4 ##############################################################
# single assign to expression sequence should still work

# This should work


#goal := proc() local a;
#   	a := 1,2,3,4;
#   	[a];
#end proc:

#optimized := proc()
#	[1,2,3,4];
#end proc:

#ped := OnPE(goal):

#got := ToInert(eval(ped[ModuleApply])):
#expected := ToInert(eval(optimized)):


Try(300, got, expected);

#######################################################################
#end test
