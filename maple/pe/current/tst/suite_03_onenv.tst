#test

# TEST SUITE 3: Online Environment #######################################

with(TestTools):
kernelopts(opaquemodules=false):

#libname := libname, "/home/mike/thesis/trunk/maple/pe/current/lib":
libname := libname, "E:\\School\\svn\\thesis\\maple\\pe\\current\\lib":

##########################################################################


##########################################################################
# tables

env := OnPE:-OnENV();

env:-putTblVal("r", "x", 99);
env:-putTblVal("r", "z", 25);
env:-putTblVal("r", "a", 15);
env:-grow();

Try(200, env:-getTblVal("r", "x"), 99);
Try(201, env:-getTblVal("r", "z"), 25);
Try(202, env:-getTblVal("r", "a"), 15);

env:-putTblVal("r", "x", 1);
env:-putTblVal("r", "y", 2);

Try(203, env:-getTblVal("r", "x"), 1);
Try(204, env:-getTblVal("r", "y"), 2);

env:-setTblValDynamic("r", "z");

t := env:-getVal("r");

Try[verify,table](205, t, table(["x"=1, "y"=2, "a"=15]));

env:-shrink();

Try(206, env:-getTblVal("r", "x"), 99);
Try(207, env:-getTblVal("r", "z"), 25);
Try(208, env:-getTblVal("r", "a"), 15);

t2 := env:-getVal("r");

Try[verify,table](209, t2, table(["x"=99, "z"=25, "a"=15]));

##########################################################################


#end test
