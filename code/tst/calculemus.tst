#test

# TEST SUITE 1: BINARY POWERING #######################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "../lib":
#######################################################################


coefflist := proc(p) local d, i;
    d := degree(p,x);
    return  [seq(coeff(p, x, d-i), i=0..d)];
end proc:

mydegree := proc(p, v) local lst, i, s;
    lst := coefflist(p, v);
    s := nops(lst);
    for i from 1 to s do
        if lst[i] <> 0 then
            return s-i
       end if;
   end do;
   return -infinity;
end proc:

goal := proc(a, b, c) local p;
    p := a*x^2+b*x+c;
    mydegree(p, x)
end proc;


opts := PEOptions();
opts:-setPropagateDynamic(true);
res1 := OnPE(goal, opts):


got := ToInert(eval(res1:-ModuleApply));

expected := ToInert(
proc(a, b, c)
    if a <> 0 then 2
    elif b <> 0 then 1
    elif c <> 0 then 0
    else -infinity
    end if
end proc
);

Try(101, got, expected);


goal2a := proc(a,b) local p; 
    p := a*x^17+b*x^12;
    mydegree(p, x);
end proc;

res2 := OnPE(goal2a, opts):
got := ToInert(eval(res2:-ModuleApply));

expected := ToInert(
proc(a, b)
    if a <> 0 then 17 
    elif b <> 0 then 12 
    else -infinity 
    end if
end proc
);

Try(102, got, expected);



goal2b := proc(a,b) local p; 
    p := a*x^17+b*x^12+3*x;
    mydegree(p, x);
end proc;

res3 := OnPE(goal2b, opts):
got := ToInert(eval(res3:-ModuleApply));

expected := ToInert(
proc(a, b) 
    if a <> 0 then 17 
    elif b <> 0 then 12 
    else 1 
    end if 
end proc
);

Try(103, got, expected);


goal2c := proc(a) local p; 
    p := (a-5)*x^17+(a^2-1)*x^12+3*x;
    mydegree(p, x);
end proc;

res4 := OnPE(goal2c, opts):
got := ToInert(eval(res4:-ModuleApply));

expected := ToInert(
proc(a)
    if a - 5 <> 0 then 17 
    elif a^2 - 1 <> 0 then 12 
    else 1 
    end if
end proc
);

Try(104, got, expected);

#######################################################################


GE := proc(AA, n, m) local B,i,j,k,r,d,s,t,rmar,pivot,ii;
B := table(); # make a copy
for ii to n do for j to m do B[ii,j] := AA[ii,j] end do end do;

rmar := min(n,m); s := 1; d := 1; r := 1;
for k to min(m,rmar) while r <= n do
    # Search for a pivot element.  Choose the first
    pivot := -1;
    for i from r to n do
        if (pivot = -1) then
            if (B[i,k] <> 0) then pivot := i; end if;
        end if;
    end do;

    if pivot>-1 then # interchange row i with row r is necessary
		if pivot <> r then
            s := -s;
            for j from k to m do
			   t := B[pivot,j]; B[pivot,j] := B[r,j]; B[r,j] := t
            end do;
		end if;
		for i from r+1 to n do
			for j from k+1 to m do
                B[i,j] := (B[i,j]*B[r,k]- B[r,j]*B[i,k])/ d;
			end do;
			B[i,k] := 0;
		end do;
        d := B[r,k];
        r := r + 1   # go to next row
    end if;
end do;			     # go to next column
eval(B);
end proc:

goal1 := proc() local A;
    A := table([(1,1)=1, (1,2)=2, (2,1)=-5, (2,2)=6]);
    GE(A, 2, 2);
end proc:
goal1();

goal2 := proc(x) local A;
    A := table([
        (1,1) = 1, (1, 2)=-2, (1,3)=3, (1,4)=1,
        (2,1) = 2, (2, 2)=x,  (2,3)=6, (2,4)=6,
        (3,1) =-1, (3, 2)=3, (3,3)=x-3, (3,4)=0]);
    GE(A, 3, 4);
end proc:


opts := PEOptions();
opts:-setInlineAssigns();

res1 := OnPE(goal1, opts): # fully static, easy

got := res1:-ModuleApply();

Try(201, got[1,1], 1);
Try(202, got[1,2], 2);
Try(203, got[2,1], 0);
Try(204, got[2,2], 16);


res2 := OnPE(goal2, opts): # the one we really care about
got := ToInert(eval(res2:-ModuleApply));

expected := ToInert(
proc(x) local B1;
    B1[2, 2] := x;
    B1[3, 3] := x - 3;
    B1[2, 2] := B1[2, 2] + 4;
    B1[3, 3] := B1[3, 3] + 3;
    if B1[2, 2] <> 0 then
        B1[3, 3] := B1[3, 3] * B1[2, 2];
        B1[3, 4] := B1[2, 2] - 4;
        if B1[3, 3] <> 0 then
            B1[1, 1] := 1;
            B1[1, 2] := -2;
            B1[1, 3] := 3;
            B1[1, 4] := 1;
            B1[2, 1] := 0;
            B1[2, 3] := 0;
            B1[2, 4] := 4;
            B1[3, 1] := 0;
            B1[3, 2] := 0;
            eval(B1)
        else
            B1[1, 1] := 1;
            B1[1, 2] := -2;
            B1[1, 3] := 3;
            B1[1, 4] := 1;
            B1[2, 1] := 0;
            B1[2, 3] := 0;
            B1[2, 4] := 4;
            B1[3, 1] := 0;
            B1[3, 2] := 0;
            B1[3, 3] := 0;
            eval(B1)
        end if
    else
        B1[2, 3] := B1[3, 3];
        B1[1, 1] := 1;
        B1[1, 2] := -2;
        B1[1, 3] := 3;
        B1[1, 4] := 1;
        B1[2, 1] := 0;
        B1[2, 2] := 1;
        B1[2, 4] := 1;
        B1[3, 1] := 0;
        B1[3, 2] := 0;
        B1[3, 3] := 0;
        B1[3, 4] := 4;
        eval(B1)
    end if
end proc
);

Try(210, got, expected);

#######################################################################

res1 := 'res1':
int_pow := proc(i,var)
    if op(1,i)=var then
        if op(2,i)=-1 then
            ln(var)
        else
            var^(op(2,i)+1)/(op(2,i)+1)
        end if
    else
        int(i,var)
    end if;
end proc:

int_sum := proc(l, var)
    local res, x, i;
    res := 0;
    for i from 1 to nops(l) do
        x := op(i, l);
        res := res + x[1]*int_pow(x[2],var);
    end do;
    res;
end proc:

goal := proc(n) local x; int_sum([[5,x^2], [-7,x^n], [2,x^(-1)]], x); end proc:

opts := PEOptions();
opts:-setPropagateDynamic(true);
opts:-addFunction(PEOptions:-INTRINSIC, ln);
res3 := OnPE(goal, opts):

got := (eval(res3:-ModuleApply));
expected := 
proc(n) local m2, res1, x;
    if n = -1 then 
        m2 := ln(x) 
    else 
        m2 := x^(n + 1)/(n + 1) 
    end if;
    res1 := 5 * x^3/3 - 7 * m2;
    res1 := res1 + 2 * ln(x);
    res1
end proc;

# This is failing right now, but I will assume it is a trivial bug to fix
#  (the issue is that x is supposed to be a local, and it's not)
Try(300, ToInert(eval(got)), ToInert(eval(expected)));

#######################################################################
#end test
