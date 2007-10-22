#test

# Generic Linear Algebra Tests ########################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "../lib":

#######################################################################

MatrixMatrixMultiplyOperations := [`0`,`+`::procedure,`*`::procedure]:

HasOperation := proc(D,f)
    # NB: assigned(D[`+`]) generates an error if D[`+`] is not an export
    if type(D,table) then assigned(D[f]) else member(f,[exports(D)]) fi;
  end:

  # Type check
  GenericCheck := proc(P,T) local D,f,n,t;
    if not type(P,indexed) or nops(P)<>1 then error "%1 is not indexed by a domain",P fi;
    D := op(1,P);
    if not type(D,{table,`module`}) then error "domain must be a table or module" fi;
    for f in T do
      if type(f,`::`) then n := op(1,f); t := op(2,f);
      elif type(f,symbol) then n := f; t := false;
      else error "invalid operation name: %1", f;
      fi;
      if not HasOperation(D,n) then error "missing operation: %1",n; fi;
      if t <> false and not type(D[n],t) then error "operation has wrong type: %1", f fi;
    od;
    D
  end: 
  
MatrixMatrixMultiply := proc(A::Matrix,B::Matrix) local D,n,p,m,C,i,j,k;
  D := GenericCheck( procname, MatrixMatrixMultiplyOperations );
  if op(1,A)[2]<>op(1,B)[1] then error 
     "first matrix column dimension (%1) <> second matrix row dimension (%2)", op(1,A)[2], op(1,B)[1]; fi;
  n,p := op(1,A);
  m := op(1,B)[2];
  C := Matrix(n,m);
  for i to n do 
     for j to m do 
        C[i,j] := D[`+`](seq(D[`*`](A[i,k],B[k,j]),k=1..p)) 
     od
  od;
  C
end:


(Z[`0`],Z[`1`],Z[`+`],Z[`-`],Z[`*`],Z[`=`]) := (0,1,`+`,`-`,`*`,`=`);
#A := Matrix([[2,1,4],[3,2,1],[0,0,5]]);
#B := Matrix([[1,2,3],[2,1,2],[3,2,1]]);



goal := proc(x,y)
	MatrixMatrixMultiply[Z](x,y);
end proc;

opts := PEOptions();
opts:-addFunction(PEOptions:-INTRINSIC, Matrix);

ps := OnPE(goal, opts);
got := ToInert(eval(ps:-ModuleApply));

expected := ToInert(proc (x, y) local n1, p1, m6, C1, i1, j1; 
	if op(1,x)[2] <> op(1,y)[1] then 
		error "first matrix column dimension (%1) <> second matrix row dimension (%2)", op(1,x)[2], op(1,y)[1] 
	end if; 
	
	n1, p1 := op(1,x); 
	m6 := op(1,y)[2]; 
	C1 := Matrix(n1,m6); 
	for i1 to n1 do 
		for j1 to m6 do 
			C1[i1,j1] := `+`(seq(x[i1,k]*y[k,j1],k = 1..p1)) 
		end do 
	end do; 
	C1 
end proc);

# ignore bug, k should have been declared as a local
got := eval(got, _Inert_LOCALNAME = proc(x) _Inert_NAME(x) end proc);

Try(101, got, expected);

#######################################################################

RingOperations := [`+`::procedure,`-`::procedure,`*`::procedure,`0`,`1`,`=`::procedure]:
BerkowitzAlgorithmOperations := RingOperations:

BerkowitzAlgorithm := proc(A::Matrix)
 local D,m,n,Vect,r,C,S,Q,i,j,k,one,zero,minusone;
 
   D := GenericCheck( procname, RingOperations );
   m,n := LinearAlgebra:-Dimensions(A);
   if m<>n then error "Matrix must be square" fi;
   one := D[`1`];
   zero := D[`0`];
   minusone := D[`-`](one);
     if n=1 then return Vector([one,D[`-`](A[1,1])]);
     elif n=2 then return Vector([one,
                              D[`-`](D[`+`](A[1,1],A[2,2])),
                              D[`-`](D[`*`](A[1,1],A[2,2]),D[`*`](A[2,1],A[1,2]))]);
     else
       Vect := Vector(n+1,'fill'=zero);
       Vect[1] := minusone;
       Vect[2] := A[1,1];
       C[1] := minusone;
       for r from 2 to n do
         for i to r-1 do S[i]:=A[i,r] od;
         C[2] := A[r,r];
         for i from 1 to r-2 do
           C[i+2] := D[`+`](seq(D[`*`](A[r,j],S[j]),j=1..r-1));
           for j to r-1 do
             Q[j] := D[`+`](seq(D[`*`](A[j,k],S[k]),k=1..r-1));
           od;
           for j to r-1 do S[j] := Q[j] od;
         od;
         C[r+1] := D[`+`](seq(D[`*`](A[r,j],S[j]),j=1..r-1));
         for i to r+1 do
           Q[i] := D[`+`](seq(D[`*`](C[i+1-j],Vect[j]),j=1..min(r,i)));
         od;
         for i to r+1 do Vect[i] := Q[i] od;
       od;
       if type(n,odd) then for i to n+1 do Vect[i] := D[`-`](Vect[i]) od fi;
       return Vect
     fi;
end:

(Z[`0`],Z[`1`],Z[`+`],Z[`-`],Z[`*`],Z[`=`]) := (0,1,`+`,`-`,`*`,`=`):

opts := PEOptions():
opts:-addFunction(PEOptions:-INTRINSIC, Vector):
opts:-addFunction(PEOptions:-INTRINSIC, 'simplify');

goal := proc(X) BerkowitzAlgorithm[Z](X) end proc;



bkz_s := proc(X) 
	local m27, largs1, m1, n1, x4, x6, x8, y1, Vect1, S1, C1, Q1, r1, i1, j1, x10; 
	
	if hastype(X,{Matrix, Vector}) then 
		if type(X,list) then 
			m27 := map(simplify,X,rtable) 
		elif type(X,set) then 
			m27 := map(simplify,X,rtable) 
		else 
			m27 := simplify(X,rtable) 
		end if 
	else 
		m27 := X 
	end if;
	 
	largs1 := [`if`(type(X,{Matrix, Vector}),X,m27)]; 
	
	if not type(largs1[1],{Matrix, Vector}) then 
		error "expects its %-1 argument, A, to be of type {Matrix,Vector}, but received %2", 1, largs1[1] 
	end if; m1, n1 := op(1,largs1[1]); 
	
	if m1 <> n1 then 
		error "Matrix must be square" 
	end if; 
	
	if n1 = 1 then 
		x4 := X[1,1]; 
		Vector([1, -x4]) 
	elif n1 = 2 then 
		x6 := X[1,1]+X[2,2]; 
		x8 := X[1,1]*X[2,2]; 
		y1 := X[2,1]*X[1,2]; 
		Vector([1, -x6, x8-y1]) 
	else 
		Vect1 := Vector(n1+1,fill = 0); 
		Vect1[2] := X[1,1]; 
		S1 := S; 
		C1[1] := -1; 
		Q1 := Q; 
		Vect1[1] := -1; 
		for r1 from 2 to n1 do 
			for i1 to r1-1 do 
				S1[i1] := X[i1,r1] 
			end do; 
			C1[2] := X[r1,r1]; 
			for i1 to r1-2 do 
				C1[i1+2] := `+`(seq(X[r1,j]*S1[j],j = 1 .. r1-1)); 
				for j1 to r1-1 do 
					Q1[j1] := `+`(seq(X[j1,k]*S1[k],k = 1 .. r1-1)) 
				end do; 
				for j1 to r1-1 do 
					S1[j1] := Q1[j1] 
				end do 
			end do; 
			C1[r1+1] := `+`(seq(X[r1,j1]*S1[j1],j1 = 1 .. r1-1)); 
			for i1 to r1+1 do 
				Q1[i1] := `+`(seq(C1[i1+1-j1]*Vect1[j1],j1 = 1 .. min(r1,i1))) 
			end do; 
			for i1 to r1+1 do 
				Vect1[i1] := Q1[i1] 
			end do 
		end do; 
		
		if type(n1,odd) then 
			for i1 to n1+1 do 
				x10 := Vect1[i1]; 
				Vect1[i1] := -x10 
			end do 
		end if; 
		
		Vect1 
	end if 
end proc;

ps := OnPE(goal, opts);
got := ToInert(eval(ps:-ModuleApply));

# workaround for bug
got := eval(got, _Inert_LOCALNAME = proc(x) _Inert_NAME(x) end proc);

expected := ToInert(eval(bkz_s));

Try(201, got, expected);

#######################################################################
#end test