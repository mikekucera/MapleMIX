#test

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "../lib":

###################################################################
#
# First case to get going, still with tables, but indirectly
#
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
    A := [table([(1,1)=1, (1,2)=2, (2,1)=-5, (2,2)=6])];
    # A := Matrix(2,2,[[1,2],[-5,6]]);
    # A := rtable(1..2,1..2,[[1,2],[-5,6]]);
    # GE(A, 2, 2);
    GE(A[1], 2, 2);
end proc:
goal1();

opts := PEOptions();
opts:-setInlineAssigns();

# infolevel[PE] := 10;
res1 := OnPE(goal1, opts); # fully static, easy

got := eval(res1:-ModuleApply());

Try(201, got[1,1], 1);
Try(202, got[1,2], 2);
Try(203, got[2,1], 0);
Try(204, got[2,2], 16);

###################################################################
#
# Second case, rtables.
#
GE := proc(AA, n, m) local B,i,j,k,r,d,s,t,rmar,pivot,ii;
B := rtable(AA); # make a copy

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

goal2 := proc() local A;
    A := rtable(1..2,1..2,[[1,2],[-5,6]]);
    # GE(A, 2, 2);
    GE(A, 2, 2);
end proc:
goal2();

infolevel[PE] := 10;
res2 := OnPE(goal2, opts); # fully static, easy

got := eval(res2:-ModuleApply());

#######################################################################
#end test
