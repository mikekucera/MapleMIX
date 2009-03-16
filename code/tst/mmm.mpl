libname := libname, "../lib";
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
A := Matrix([[2,1,4],[3,2,1],[0,0,5]]);
B := Matrix([[1,2,3],[2,1,2],[3,2,1]]);
MatrixMatrixMultiply[Z](A,B);

goal := proc(x,y)
MatrixMatrixMultiply[Z](x,y);
end proc;

#infolevel[PE] := 4;

opts := PEOptions();
opts:-addFunction(PEOptions:-INTRINSIC, Matrix);
# printlevel := 1000;

ps := OnPE(goal, opts);
print(ps:-ModuleApply);
