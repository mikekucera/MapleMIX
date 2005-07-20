read "jcpe.mpl":
interface(echo=0);
N := 23:

e1 := proc() 5 end:
e2 := proc() x end:
e3 := proc() x+y end:
e4 := proc() 3*x-5*y end:
e5 := proc() 5+x*y end:
e6 := proc() x+y+4 end:
e7 := proc() 1+x*(1+x*(1+x)) end:
e8 := proc() g(x+1,y-3,z+5) end:
e9 := proc() f(x,y) end:
e10 := proc() h(x,y,z) end:
e11 := proc() `+`(1,1) = 2 end:
e12 := proc() `+`(1,1) = 3 end:
e13 := proc() `+`(1.1,1) end:
e14 := proc() `^`(5,2) end:
e15 := proc() 1<2 and 5 <= 6 end:
e16 := proc() `^`(I,2)+1=0 end:
e17 := proc() if 0=0 then 1 else 2 end if end:
e18 := proc() if 0=1 then 1 else 2 end if end:
e19 := proc() if 0=1 then `^`(0,-1) else 2 end if end:
e20 := proc() [1+x, 1+y] end:
e21 := proc() {x,3} end:
e22 := proc() sin(0) end:
e23 := proc() proc(x) x^2 end(2) end:

for i to N do te||i := ToInert(eval(e||i)) end do:

bte := table('defined',["x"=Dyn,"y"=Dyn,"z"=Dyn, "f"=Dyn,"g"=Dyn,"h"=Dyn]):
r1 := proc() 5 end:
r2 := proc() x end:
r3 := proc() x + y end:
r4 := proc() 3*x-5*y end:
r5 := proc() 5+x*y end:
r6 := proc() x+y+4 end:
r7 := proc() 1+x*(1+x*(1+x)) end:
r8 := proc() g(x+1,y-3,z+5) end:
r9 := proc() f(x,y) end:
r10 := proc() h(x,y,z) end:
r11 := proc() true end:
r12 := proc() false end:
r13 := proc() 2.1 end:
r14 := proc() 25 end:
r15 := proc() true end:
r16 := proc() true end:
r17 := proc() 1 end:
r18 := proc() 2 end:
r19 := proc() 2 end:
r20 := proc() [1+x,1+y] end:
r21 := proc() {3,x} end:
r22 := proc() 0 end:
r23 := proc() 4 end:

printf("First run\n");
#for i to N do
for i from N to N do
printlevel := 200;
    res := myPE[pe_test](te||i, bte);
	# test needs to be done on Inert form!
	res1 := ToInert(eval(res));
	expect := ToInert(FromInert(ToInert(eval(r||i))));
	if not (res1 = expect) then
	    printf("Test case %d failed: got %a, expected %a\n", i, res1,
		    expect);
	    printf("   in Maple form: got %a, expected %a\n", FromInert(res1),
		    FromInert(expect));
	else 
	    printf("Test case %d passed\n", i);
	end if;
end do;

quit

#######################################################################

x := 3:
y := -1:
z := -3:
bte1 := table(["x"=Stat,"y"=Stat,"z"=Stat, "f"=Dyn,"g"=Dyn,"h"=Dyn]):
# The results below are the only ones to change
r2 := proc() 3 end proc:
r3 := proc() 2 end proc:
r4 := proc() 14 end proc:
r5 := proc() 2 end proc:
r6 := proc() 6 end proc:
r7 := proc() 40 end proc:
r8 := proc() g(4,-4,2) end proc:
r9 := proc() f(3,-1) end proc:
r10 := proc() h(3,-1,-3) end proc:
r20 := proc() [4,0] end:
r21 := proc() {3} end:

printf("Second run\n");
for i to N do
# for i from 2 to 2 do
# printlevel := 250;
    res := myPE[pe_test](te||i, bte1);
	res1 := ToInert(eval(res));
	expect := ToInert(FromInert(ToInert(eval(r||i))));
	if not (res1 = expect) then
	    printf("Test case %d failed: got %a, expected %a\n", i, res1,
		    expect);
	    printf("   in Maple form: got %a, expected %a\n", FromInert(res1),
		    FromInert(expect));
	else 
	    printf("Test case %d passed\n", i);
	end if;
end do:

#######################################################################

bte2 := table(["x"=Dyn,"y"=Stat,"z"=Stat,"f"=Dyn,"g"=Dyn,"h"=Dyn]):
x := 'x':

r2 := proc() x end proc:
r3 := proc() x-1 end proc:
r4 := proc() 3*x+5 end proc:
r5 := proc() 5-x end proc:
r6 := proc() x+3 end proc:
r7 := proc() 1+x*(1+x*(1+x)) end proc:
r8 := proc() g(1+x,-4,2) end proc:
r9 := proc() f(x,-1) end proc:
r10 := proc() h(x,-1,-3) end proc:
r20 := proc() [1+x,0] end:
r21 := proc() {3,x} end:

printf("Third run\n");
for i to N do
    res := myPE[pe_test](te||i, bte2);
	res1 := ToInert(eval(res));
	expect := ToInert(FromInert(ToInert(eval(r||i))));
	if not (res1 = expect) then
	    printf("Test case %d failed: got %a, expected %a\n", i, res1,
		    expect);
	    printf("   in Maple form: got %a, expected %a\n", FromInert(res1),
		    FromInert(expect));
	else 
	    printf("Test case %d passed\n", i);
	end if;
end do:

#######################################################################

bte3 := table(["x"=Stat,"y"=Stat,"z"=Stat,"f"=Stat,"g"=Dyn,"h"=Stat]):
r2 := proc() 3 end proc:
r3 := proc() 2 end proc:
r4 := proc() 14 end proc:
r5 := proc() 2 end proc:
r6 := proc() 6 end proc:
r7 := proc() 40 end proc:
r8 := proc() g(4,-4,2) end proc:
r9 := proc() -1 end proc:
r10 := proc() -6 end proc:
r20 := proc() [4,0] end:
r21 := proc() {3} end:
x := 3:
f := proc(x,y) if x=1 then 1 elif x=2 then 2 else y end if end proc:
h := proc(x,y,z) x*y+z end:

printf("Fourth run\n");
for i to N do
    res := myPE[pe_test](te||i, bte3);
	res1 := ToInert(eval(res));
	expect := ToInert(FromInert(ToInert(eval(r||i))));
	if not (res1 = expect) then
	    printf("Test case %d failed: got %a, expected %a\n", i, res1,
		    expect);
	    printf("   in Maple form: got %a, expected %a\n", FromInert(res1),
		    FromInert(expect));
	else 
	    printf("Test case %d passed\n", i);
	end if;
end do:
