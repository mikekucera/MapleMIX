#test

# TEST SUITE 3: Online Environment #######################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":

##########################################################################

env := OnPE:-OnENV();

Try(101, env:-putVal(x, 1), 1);
Try(102, env:-valIndices(), ["x"]);
Try(103, env:-isStatic(x), true);
Try(104, env:-isDynamic(x), false);
Try(105, env:-putVal(x,2), 2);
Try(106, env:-getVal(x), 2);

env2 := OnPE:-OnENV:-NewOnENV();
env2:-putVal(y, 9);

c := env:-combine(env2);

Try(201, c:-getVal(x), 2);
Try(202, c:-getVal(y), 9);

env3 := OnPE:-OnENV:-NewOnENV();
env3:-putType(z, integer);

c2 := env3:-combine(c);

Try(203, c2:-getVal(x), 2);
Try(204, c2:-getVal(y), 9);
Try(205, c2:-getType(z), integer);

##########################################################################


#end test
