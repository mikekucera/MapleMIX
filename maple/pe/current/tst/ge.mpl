# Fraction free Gaussian Elimination:
#
# Purpose:	Reduce the matrix A to upper triangular form.
#
# Input:	Matrix, dimension n
# Output:	reduced matrix
#

libname := libname, "lib":
kernelopts(opaquemodules=false):

GE := proc(AA, n, m)
local B,i,j,k,r,d,s,t,rmar,pivot,ii;

# make a copy
B := table();
for ii to n do for j to m do B[ii,j] := AA[ii,j] end do end do;

rmar := min(n,m);
s := 1;
d := 1;
r := 1;
for k to min(m,rmar) while r <= n do

    # Search for a pivot element.  Choose the first
    pivot := -1;
    for i from r to n do
        if (pivot = -1) then
            if (B[i,k] <> 0) then
                pivot := i;
            end if;
        end if;
    end do;
    # for i from r to n while B[i,k] = 0 do end do;

    if pivot>-1 then
		# interchange row i with row r is necessary
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
        r := r + 1      	# go to next row
    end if;
end do;			  # go to next column

eval(B);
end proc:

goal1 := proc()
    local A;
    A := table([(1,1)=1, (1,2)=2, (2,1)=-5, (2,2)=6]);
    GE(A, 2, 2);
end proc:
goal1();

goal2 := proc(x)
    local A;
    A := table([
        (1,1) = 1, (1, 2)=-2, (1,3)=3, (1,4)=1,
        (2,1) = 2, (2, 2)=x,  (2,3)=6, (2,4)=6,
        (3,1) =-1, (3, 2)=3, (3,3)=x-3, (3,4)=0]);
    GE(A, 3, 4);
end proc:
# to see what it looks like
Matrix(3, 4, goal2(y));

# for one special case
goal2b := proc()
    local A,x;
    x := -4;
    A := table([
        (1,1) = 1, (1, 2)=-2, (1,3)=3, (1,4)=1,
        (2,1) = 2, (2, 2)=x,  (2,3)=6, (2,4)=6,
        (3,1) =-1, (3, 2)=3, (3,3)=x-3, (3,4)=0]);
    GE(A, 3, 4);
end proc:
Matrix(3, 4, goal2b());

# the other special case
goal2c := proc()
    local A,x;
    x := 0;
    A := table([
        (1,1) = 1, (1, 2)=-2, (1,3)=3, (1,4)=1,
        (2,1) = 2, (2, 2)=x,  (2,3)=6, (2,4)=6,
        (3,1) =-1, (3, 2)=3, (3,3)=x-3, (3,4)=0]);
    GE(A, 3, 4);
end proc:
Matrix(3, 4, goal2c());

res1 := OnPE(goal1): # fully static, easy

res2 := OnPE(goal2): # the one we really care about

print(res1:-ModuleApply);
res1();

print(res2:-ModuleApply);

Matrix(3,4, res2(a));

Matrix(3,4, res2(0));

Matrix(3,4, res2(-4));


