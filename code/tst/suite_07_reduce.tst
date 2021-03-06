#test

# TEST SUITE 7: Reducing Expressions ##################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "../lib":

# TEST 1: MCatenate ###################################################


m := MCatenate(MName("a"), MName("b"));

Try(101, OnPE:-ReduceExp:-Reduce(m), MStatic(ab));

a := 1;

Try(102, OnPE:-ReduceExp:-Reduce(MName("a")), MStatic(1));
Try(103, OnPE:-ReduceExp:-Reduce(m), MStatic(ab));

b := 1;

Try(104, OnPE:-ReduceExp:-Reduce(m), MStatic(a1));

m1 := M:-ToM(ToInert('a || (1..5)'));

Try(105, OnPE:-ReduceExp:-Reduce(m1), MStatic(a1, a2, a3, a4, a5));

m2 := M:-ToM(ToInert('a || (1,2,3,4,5)'));

Try(106, OnPE:-ReduceExp:-Reduce(m2), MStatic(a1, a2, a3, a4, a5));


#######################################################################


#end test
