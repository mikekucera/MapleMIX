#
# GenericLinearAlgebra is a set of generic algorithms for basic
# linear algebra operations.  Below is text for the main help page.
# 
# Authors Simon Lo and Michael Monagan, MITACS project, August 2005.
#
# Updated MBM September 2005: changed output functionality of LinearSolve,
# HermiteForm, SmithForm, and HessenbergForm to use output=[...] to be
# consistent with LinearAlgebra..
#
# Updated RP March 2006: LinearSolve accepts Matrix right hand side
#                        Determinant, RREF use Bareiss method if possible
#
# Output format for GaussianElimination[F](A,'r','d') ?
# Also, BareissAlgorithm, ReducedRowEchelonForm, RREF
#

unprotect(GenericLinearAlgebra):

## Overview of the GenericLinearAlgebra Package
##
## The GenericLinearAlgebra package provides generic implementations of
## algorithms for linear algebra over fields, Euclidean domains, integral 
## domains and rings.
##
##Description(help)
##
## We show an example of how to use the MatrixInverse operation in the 
## package to invert a matrix A over a field.  The calling sequence is
##
##    MatrixInverse[F](A); 
##
## The indexed parameter F is called the domain of computation.  For the
## matrix inverse operation, it must define the operations of a field, namely,
## addition, subtraction, multiplication and division of elements of F.  It
## must also define the 0 and 1 of the field and a boolean procedure for testing
## if two elements are equal or not.  To achieve this the parameter F must
## be a table or module with the following procedures and constants:
##
##     F[`+`] : a procedure for adding zero or more elements of F
##     F[`-`] : a procedure for negating or subtracting elements of F
##     F[`*`] : a procedure for multiplying two elements of F
##     F[`/`] : a procedure for dividing two elements of F
##     F[`0`] : a constant, the additive identity of F
##     F[`1`] : a constant, the multipliciative identity of F
##     F[`=`] : a boolean procedure for comparing two elements of F
##
## To implement F for the field of rational numbers Q, because Maple has
## procedures for doing arithmetic with rational numbers, it is easy to
## code F as follows
##
##   > F[`0`] := 0:
##   > F[`1`] := 1:
##   > F[`=`] := proc(x,y) evalb( x=y ) end:
##   > F[`+`] := `+`:
##   > F[`-`] := `-`:
##   > F[`*`] := `*`:
##   > F[`/`] := `/`:
##
## To use F we do
##
##   > with(GenericLinearAlgebra):
##   > A := Matrix([[1,2,3],[2,1,2],[3,2,1]]);
##                                   [1    2    3]
##                                   [           ]
##                              A := [2    1    2]
##                                   [           ]
##                                   [3    2    1]
##
##   > MatrixInverse[F](A);
##                             [-3/8    1/2    1/8 ]
##                             [                   ]
##                             [1/2     -1     1/2 ]
##                             [                   ]
##                             [1/8     1/2    -3/8]
##
## The code for MatrixInverse is generic.  It can be used to invert a
## matrix over any field, we just need to define the required operations.
## Let's do it for a finite field.  We will represent elements of GF(27)
## as polynomials in z over the integers modulo 3.  That is, we represent
## elements of the field as polynomials modulo m(z), an irreducible
## polynomial of degree 3 in z.  We will assume that elements of the
## field are reduced, i.e., have degree less than 3.
##
##   > p := 3;
##   > m := z^3+2*z+1;
##   > GF27[`0`] := 0:
##   > GF27[`1`] := 1:
##   > GF27[`=`] := proc(a,b) evalb(a=b) end:
##   > GF27[`+`] := proc() `+`(args) mod p end:
##   > GF27[`-`] := proc(a,b) if nargs=1 then -a mod p else a-b mod p fi end:
##   > GF27[`*`] := proc(a,b) Rem(a*b,m,z) mod p; end: 
##   > GF27[`/`] := proc(a,b) local i;
##   >                if b=0 then error "division by zero" fi;
##   >                Gcdex(b,m,z,'i') mod p;
##   >                Rem(a*i,m,z) mod p;
##   >              end:
##   >
##   > A := Matrix([[1,z,z^2],[z,1,z],[z^2,z,1]]);
##                                 [            2]
##                                 [1     z    z ]
##                                 [             ]
##                            A := [z     1    z ]
##                                 [             ]
##                                 [ 2           ]
##                                 [z     z    1 ]
## 
##   > B := MatrixInverse[GF27](A);
##                            [            2          ]
##                            [ z       2 z        0  ]
##                            [                       ]
##                       B := [   2                  2]
##                            [2 z     2 z + 2    2 z ]
##                            [                       ]
##                            [            2          ]
##                            [ 0       2 z        z  ]
## 
## 
##   > MatrixMatrixMultiply[GF27](A,B);
##                                [1    0    0]
##                                [           ]
##                                [0    1    0]
##                                [           ]
##                                [0    0    1]
## 
##
##- In the above example we showed the use of the MatrixMatrixMultiply routine
##  to check that the inverse really is the inverse.
##
##
## List of GenericLinearAlgebra Package Commands
##
##    BerkowitzAlgorithm, CharacteristicPolynomial, Determinant
##    BareissAlgorithm, GaussianElimination,
##    HessenbergAlgorithm, HessenbergForm, HermiteForm, LinearSolve,
##    MatrixMatrixMultiply, MatrixInverse, MatrixVectorMultiply,
##    MinorExpansion, NullSpace, ReducedRowEchelonForm, RREF,
##    SmithForm, StronglyConnectedBlocks;
##
## Notes on the definition of the domains.
##
##- The domain may be a Maple table or a Maple module.
##
##- A common mistake is to forget to specify the domain of computation.
##  If you do this you will get an error.  For example
##
##    > MatrixInverse(A); # should be MatrixInverse[GF27](A);
##    Error, (in GenericCheck) MatrixInverse is not indexed by a domain
##
##- Another common error is to omit one of the operations in the domain.
##  The package checks that the required operations are defined and of
##  type procedure (or constant).  Here is an example of an error
##
##    > HermiteForm[GF27](A);
##    Error, (in GenericCheck) missing operation: Gcdex
##
##- The required operations for the domain of computation F for 
##  each algorithm are specified in the help page for that algorithm.
##  The package been designed to keep this list minimal.
##  Note, even if the algorithm requires a field, it may not use all of
##  the basic operations from a field, for example, the algorithm for
##  Gaussian elimination does not use addition.  Nevertheless,
##  addition is a required operation.
##
##- The additive identity `0` may or may not be unique.  The algorithms
##  will always use the following to test for zero
##     if F[`=`](x,F[`0`]) then ... else ... end if.
##  Other elements of a ring, including 1, do not need a unique representation.
##
##Description(spec)
##
##- The package exports algorithms and commands for linear algebra which 
##  are parametrized by the ring in which the matrix entries lie.
##  The package also exports algorithms.  For example, the Bareiss 
##  fraction-free algorithm is well known.  It is an algorithm which
##  computes the determinant of a matrix over any integral domain D.
##  It assumes exact division and does O(n^3) operations from D.
##  The Berkowitz algorithm is division free and takes O(n^4) operations.
##  The output matrix B over D satisfies certain properties, in particular,
##  B[i,i] is the determinant (up to sign) of the principal i by i minor.
##  So one can compute the determinant using this algorithmn by doing
##  > Determinant[D](A,method=BareissAlgorithm);
##  and also, one can compute the matrix B by doing
##  > BareissAlgorithm[D](A);
##
##EXAMPLES
##
## Suppose we want to compute the determinant of a matrix of integers
## modulo a composite integer n using the Berkowitz algorithm.  We need
## to first define the ring of integers modulo n as a domain.
##
##> with(GenericLinearAlgebra):
##> R := module() export `0`,`1`,`=`,`+`,`-`,`*`;
##>    `0` := 0;
##>    `1` := 1;
##>    `=` := proc(x,y) evalb(x=y) end;
##>    `+` := proc() :-`+`(args) mod n end;
##>    `*` := proc(a,b) a*b mod n; end;
##>    `-` := proc(a,b) if nargs=1 then -a mod n else a-b mod n fi; end;
##>    end;
###
###       R := module() export `0`, `1`, `=`, `+`, `-`, `*`;  end module
###
##> n := 6:
##> R[`*`](2,4); # check that multiplication is working
##< 2;
###
###                                    2
###
##> A := Matrix([[2,3,4,5],[3,4,1,2],[4,1,1,5],[3,1,5,4]]):
##> Determinant[R](A,method=BerkowitzAlgorithm);
##< 3;
###
###                                     3
###
## A more efficient algorithm is the Bareiss fraction free algorithm.
## It assumes only exact division and computes the determinant in O(n^3)
## operations in R.  Hence it is valid for the integers.  We illustrate
## this time using a table Z of operations for the ring.
##
##> Z[`0`], Z[`1`] := 0,1;
##> Z[`+`], Z[`-`], Z[`*`], Z[`=`] := `+`, `-`, `*`, `=`;
##> Z[Divide] := proc(x,y) evalb( irem(x,y,args[3..nargs])=0 ) end:
##> A := M
##> A := Matrix([[2,3,4,5],[3,4,1,2],[4,1,1,5],[3,1,5,4]]):
##> Determinant[Z](A,method=BareissAlgorithm);
##< 195;
##> BareissAlgorithm[Z](A);
###                         [2     3      4      5]
###                         [                     ]
###                         [0    -1    -10    -11]
###                         [                     ]
###                         [0     0    -43    -50]
###                         [                     ]
###                         [0     0      0    195]
##
## Given a matrix A of algebraic numbers which were input using Maple's
## RootOf notation, suppose we want to compute the nullspace of A. 
## We will convert to a univariate polynomial representation for the
## computation to obtain greater efficiency.
##
##> ANNullSpace := proc(AA::Matrix,rof::RootOf) 
##> local M,z,R,m,n,i,j,A,F,B;
##>    M := subs(_Z=z,op(1,rof)); # extract the minimal polynomial
##>    R := polynom(rational,z); # the data type of the elements
##>    if not type(M,R) then error "invalid RootOf" fi;
##>    m,n := LinearAlgebra:-Dimensions(AA);
##>    A := Matrix(m,n);
##>    for i to m do for j to n do
##>       A[i,j] := subs(rof=z,AA[i,j]); # convert into Q[z]
##>       if not type(A[i,j],R) then error "invalid matrix entries" fi;
##>       A[i,j] := rem(A[i,j],M,z); # reduce the entries
##>    end do end do;
##>    F[`0`] := 0; F[`1`] := 1;
##>    F[`=`] := `=`; F[`+`] := `+`; F[`-`] := `-`;
##>    F[`*`] := proc(a,b) rem(a*b,M,z) end;
##>    F[`/`] := proc(a,b) local i;
##>       if b=0 then error "division by zero" fi;
##>       if gcdex(b,M,z,'i')<>1 then error "invalid RootOf" fi;
##>       rem(a*i,M,z);
##>    end:
##>    B := GenericLinearAlgebra:-NullSpace[F](A);
##>    subs( z=rof, B ); # convert back to the RootOf represenation
##> end:
##>
##> a := RootOf(z^3-2);
##> M := Matrix([[1,a,a^2],[a+a^2,a+a^2,3],[a^2,a,1]]);
###
###                          [                     2]
###                          [  1         a       a ]
###                          [                      ]
###                          [     2         2      ]
###                          [a + a     a + a     3 ]
###                          [                      ]
###                          [   2                  ]
###                          [  a         a       1 ]
###
##> B := ANNullSpace(M,a);
##< {<1,-a^2/2-a,1>};
###                                [     1     ]
###                                [           ]
###                          B := {[      2    ]}
###                                [-1/2 a  - a]
###                                [           ]
###                                [     1     ]
###
###
### For the last example, we compute the nullspace of a matrix
### of complex rationals.
###
##> C[`0`] := 0:
##> C[`1`] := 1:
##> C[`=`] := `=`:
##> C[`+`] := `+`:
##> C[`-`] := `-`:
##> C[`*`] := `*`:
##> C[`/`] := `/`:
##> 
##> A := Matrix([[1,I,-I],[3,-1+I,-4*I],[I,1-I,2]]);
### 
### 
###                                    [1      I        -I ]
###                                    [                   ]
###                               A := [3    -1 + I    -4 I]
###                                    [                   ]
###                                    [I    1 - I      2  ]
### 
##> B := NullSpace[C](A);
##< {<(-1+7*I)/5,(-2-I)/5,1>};
###                                        [-1/5 + 7/5 I]
###                                        [            ]
###                                  B := {[-2/5 - 1/5 I]}
###                                        [            ]
###                                        [     1      ]
### 
### To check that the answer is correct we need to verify that A.B[1] = 0.
### We will write a procedure to do this.  This illustrates how the
### procedures in the GenericLinearAlgebra are coded.  The GenericCheck
### procedure checks that the procedure call was called with a domain
### (a table or module) and that it has the given values (exports).
###
##> MatrixTimesVector := proc(A::Matrix,v::Vector) local D,n,p,m,C,i,k;
##>   D := GenericCheck( procname, [`0`,`+`,`*`] );
##>   n,p := op(1,A);
##>   m := op(1,v);
##>   if p<>m then error "incompatible dimensions" fi; 
##>   C := Vector(n,'fill'=D[`0`]);
##>   for i to n do
##>     for k to p do C[i] := D[`+`](C[i],D[`*`](A[i,k],v[k])) od;
##>   od;
##>   C;
##> end:
##> MatrixTimesVector[C](A,B[1]);
##< <0,0,0>;
##                                        [0]
##                                        [ ]
##                                        [0]
##                                        [ ]
##                                        [0]
##


GenericLinearAlgebra := module()

export
        BerkowitzAlgorithm,
        CharacteristicPolynomial,
        Determinant,
        BareissAlgorithm,
        GaussianElimination,
        GenericCheck,
        HessenbergAlgorithm,
        HessenbergForm,
        HermiteForm,
        LinearSolve,
        MatrixMatrixMultiply,
        MatrixInverse,
        MatrixVectorMultiply,
        MinorExpansion,
        NullSpace,
        ReducedRowEchelonForm,
        RREF, # synonym for ReducedRowEchelonForm
        SmithForm,
        StronglyConnectedBlocks;

local
        HasOperation,
        StronglyConnectedBlocksOperations,
        BerkowitzAlgorithmOperations,
        DeterminantOperations,
        MinorExpansionOperations,
        MatrixMatrixMultiplyOperations,
        BareissAlgorithmOperations,
        HessenbergFormOperations,
        HessenbergAlgorithmOperations,
        GaussianEliminationOperations,
        ReducedRowEchelonFormOperations,
        MatrixInverseOperations,
        NullSpaceOperations,
        LinearSolveOperations,
        HermiteFormOperations,
        SmithFormOperations,
        RingOperations,
        DomainOperations,
        FieldOperations,
        EuclidDomainOperations;

option package;

  # Operations
  RingOperations := [`+`::procedure,`-`::procedure,`*`::procedure,`0`,`1`,`=`::procedure]:
  DomainOperations := [`+`::procedure,`-`::procedure,`*`::procedure,Divide::procedure,`0`,`1`,`=`::procedure]:
  EuclidDomainOperations := [`+`::procedure,`-`::procedure,`*`::procedure,Gcdex::procedure,
     Quo::procedure,Rem::procedure,
     UnitPart::procedure,EuclideanNorm::procedure,`0`,`1`,`=`::procedure]:
  FieldOperations := [`+`::procedure,`-`::procedure,`*`::procedure,`/`::procedure,`=`::procedure,`0`,`1`]:
  StronglyConnectedBlocksOperations := [`0`,`=`::procedure]:
  BerkowitzAlgorithmOperations := RingOperations;
  MinorExpansionOperations := RingOperations;
  DeterminantOperations := RingOperations;
  MatrixMatrixMultiplyOperations := [`0`,`+`::procedure,`*`::procedure]:
  BareissAlgorithmOperations := DomainOperations;
  HessenbergFormOperations := FieldOperations;
  HessenbergAlgorithmOperations := FieldOperations;
  GaussianEliminationOperations := FieldOperations;
  ReducedRowEchelonFormOperations := FieldOperations:
  MatrixInverseOperations := FieldOperations:
  NullSpaceOperations := FieldOperations:
  LinearSolveOperations := FieldOperations:
  HermiteFormOperations := EuclidDomainOperations;
  SmithFormOperations := EuclidDomainOperations;

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
  

# Routines


## CALLINGSEQ
##- StronglyConnectedBlocks[R](A)
##
##PARAMETERS
##- R     : the domain of computation
##- A     : a square matrix of values in R
##
##RETURNS
##
##- StronglyConnectedBlocks[R](A) return sequence of the form m, [A1,A2,...,Ak] where
##  each Ai is a matrix, a permuted submatrix of A, and m = dim(A)-dim(A1)-...-dim(Ak)
##
##
##SYNOPSIS
##
##- Viewing A as the adjancency matrix of a graph G, first compute the strongly connected components of G:
##  V1, V2, V3, ..., Vk, where Vi = {vi_1, vi_2, vi_3, ..., vi_ni}
##
##- Returns the submatrices of A, denoted Ai, where the rows and columns of Ai are rows Vi and columns Vi of A
##
##- The Ai corresponds to the diagonal blocks of some row and column permutations of A.
##
##- Zero blocks are not returned as Ai, instead returns m such that m = dim(A)-dim(A1)-...-dim(Ak).
##  i.e. m is the sum of the dimensions of the zero blocks.
##
##- The returned m and Ai satisfies:
##    If m=0 then
##      det(A) = prod(det(Ai),i=1..k)
##      charpoly(A,x) = prod(charpoly(Ai,x),i=1..k)
##
##    Else
##      det(A) = 0
##      charpoly(A,x) = x^m * prod(charpoly(Ai,x),i=1..k)
##  
##  
##- The (indexed) parameter R, which specifies the domain (only requirement is that 0 is uniquely defined).
##  R must be a Maple table (module) which has the following values (exports):
##
##  R[`0`] : a constant for the zero of the domain R
##  R[`=`] : a boolean procedure for testing if two elements of R are equal
## 
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> R[`0`],R[`=`] := 0,`=`:               
##
##
## 
##> A := Matrix([[a,b,c,d],[e,f,g,h],[0,0,k,l],[0,0,0,0]]);
##                               [a    b    c    d]
##                               [                ]
##                               [e    f    g    h]
##                          A := [                ]
##                               [0    0    k    l]
##                               [                ]
##                               [0    0    0    0]
##
## 
##> StronglyConnectedBlocks[R](A);
##                                     [a    b]
##                            1, [[k], [      ]]
##                                     [e    f]
##
##> A := Matrix([[0, 0, 0, 1], [1, 0, 0, 1], [1, 1, 0, 1], [0, 0, 0, 0]]);
##                               [0    0    0    1]
##                               [                ]
##                               [1    0    0    1]
##                          A := [                ]
##                               [1    1    0    1]
##                               [                ]
##                               [0    0    0    0]
##
##> StronglyConnectedBlocks[R](A);                         
##                                   4, []
##
##
##
StronglyConnectedBlocks := proc(A::Matrix)
local D,s,StrongConnect,i,j,Stack,top,Number,Lowlink,OnStack,u,n,m,k,SCC,t,M,S,B,C,zero;
   D := GenericCheck( procname, StronglyConnectedBlocksOperations );
   zero := D[`0`];
   StrongConnect := proc(v)
   local w;
      i := i+1;
      Number[v] := i;
      Lowlink[v] := i;
      top := top+1;
      Stack[top] := v;
      OnStack[v] := true;
      for w in M[v] do
         if Number[w] = 0 then
            StrongConnect(w);
            Lowlink[v] := min(Lowlink[v],Lowlink[w])
         elif Number[w] < Number[v] then
            if OnStack[w] then
               Lowlink[v] := min(Lowlink[v],Number[w])
            end if
         end if
      end do;
      if Lowlink[v] = Number[v] then
         t := top;
         while t>0 and Number[Stack[t]] >= Number[v] do
            OnStack[Stack[t]] := false;
            t := t-1;
         end do;
         SCC[k] := [seq(Stack[j],j=t+1..top)];
         top := t;
         k := k+1
      end if
   end proc:

   n,m := op(1,A);
   if n<>m then error "Matrix must be square" fi;
   M := [seq([seq(`if`(D[`=`](A[i,j],zero),NULL,j),j=1..n)],i=1..n)];
   i := 0;
   k := 1;
   Stack := Array(1..n);
   top := 0;
   Number := Array(1..n);
   Lowlink := Array(1..n);
   OnStack := Array(1..n,'fill'=false);
   for u to n do
      if Number[u] = 0 then StrongConnect(u) end if
   end do;
   if nops(SCC[1])=n then return 0,[A]fi;
   B := [seq(`if`(nops(SCC[i])=1 and D[`=`](A[op(SCC[i]),op(SCC[i])],zero), NULL, A[SCC[i],SCC[i]]),i=1..k-1)];
   k-1-nops(B), B;
end proc:
  

## CALLINGSEQ
##- BerkowitzAlgorithm[R](A)
##
##PARAMETERS
##- R     : a table or module, the domain of computation
##- A     : square matrix of values in R
##
##RETURNS
##- BerkowitzAlgorithm[R](A) returns a vector of values from R encoding
##  the characteristic polynomial of A.
##
##SYNOPSIS
##- Given an n by n matrix A of values from a commutative ring R,
##  BerkowitzAlgorithm[R](A) returns a vector V of dimension n+1 of values in R
##  with the coefficients of the characteristic polynomial of A.  The characteristic
##  polynomial is the polynomial V[1]*x^n + V[2]*x^(n-1) + ... + V[n]*x + V[n+1].
##  The Berkowitz algorithm does O(n^4) multiplications and additions in R.
##
##- The (indexed) parameter R, which specifies the domain, a commutative ring,
##  must be a Maple table (module) which has the following values (exports):
##
##  R[`0`] : a constant for the zero of the ring R
##  R[`1`] : a constant for the (multiplicative) identity of R
##  R[`+`] : a procedure for adding elements of R (nary)
##  R[`-`] : a procedure for negating and subtracting elements of R (unary and binary)
##  R[`*`] : a procedure for multiplying elements of R (binary and commutative)
##  R[`=`] : a boolean procedure for testing if two elements of R are equal
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Z[`0`],Z[`1`],Z[`+`],Z[`-`],Z[`*`],Z[`=`]) := (0,1,`+`,`-`,`*`,`=`):
##> A := Matrix([[2,1,4],[3,2,1],[0,0,5]]);
##
##                                   [2    1    4]
##                                   [           ]
##                              A := [3    2    1]
##                                   [           ]
##                                   [0    0    5]
##
##> C := BerkowitzAlgorithm[Z](A);
##                                       [ 1]
##                                       [  ]
##                                       [-9]
##                                  C := [  ]
##                                       [21]
##                                       [  ]
##                                       [-5]
##
##> add(C[i+1]*x^(3-i),i=0..3);                  
##                            3      2
##                           x  - 9 x  + 21 x - 5
##
 
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

## CALLINGSEQ
##- MinorExpansion[R](A)
##
##PARAMETERS
##- R     : the domain of computation, a commutative ring
##- A     : a square matrix of values in R
##
##RETURNS
##
##- MinorExpansion[R](A) returns an element of the ring R, the determinant of A.
##
##SYNOPSIS
##- The (indexed) parameter R, which specifies the domain, a commutative ring,
##  must be a Maple table (module) which has the following values (exports):
##
##  R[`0`] : a constant for the zero of the ring R
##  R[`1`] : a constant for the (multiplicative) identity of R
##  R[`+`] : a procedure for adding elements of R (nary)
##  R[`-`] : a procedure for negating and subtracting elements of R (unary and binary)
##  R[`*`] : a procedure for multiplying elements of R (binary and commutative)
##  R[`=`] : a boolean procedure for testing if two elements of R are equal
## 
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (R[`0`],R[`1`],R[`+`],R[`-`],R[`=`]) := (0,1,`+`,`-`,`=`);
##
##             R[0], R[1], R[+], R[-], R[=] := 0, 1, +, -, *, =
##
##> R[`*`] := proc(f,g) expand(f*g) end: # polynomial multiplication
##
## 
##> A := Matrix([[u,v,w],[v,u,v],[w,v,u]]);
##                                    [u    v    w]
##                                    [           ]
##                               A := [v    u    v]
##                                    [           ]
##                                    [w    v    u]
## 
##> MinorExpansion[R](A);
##                           3        2        2    2
##                          u  - 2 u v  + 2 w v  - w  u
##

MinorExpansion := proc(A::Matrix) local D,m,n,zero,minor;
  D := GenericCheck( procname, MinorExpansionOperations );
  zero := D[`0`];
  minor := subsop(4=NULL, proc(A,r,c,n) local i,t,d; option remember;
    if n=1 then d := A[r[1],c[1]]
    elif n=2 then d:= D[`-`](D[`*`](A[r[1],c[1]],A[r[2],c[2]]),D[`*`](A[r[1],c[2]],A[r[2],c[1]]))
    else
      t := subsop(1=NULL,c);
      d := zero;
      for i to n do
        if not D[`=`](A[r[i],c[1]],zero) then
          d := `if`(type(i,odd),D[`+`](d,D[`*`](A[r[i],c[1]],procname(A,subsop(i=NULL,r),t,n-1))),
                                D[`-`](d,D[`*`](A[r[i],c[1]],procname(A,subsop(i=NULL,r),t,n-1))))
        fi
      od;
    fi;
    d;
  end):
  m,n := LinearAlgebra:-Dimensions(A);
  if m<>n then error "Matrix must be square" fi;
  minor(A,[$1..n],[$1..n],n);
end:

## CALLINGSEQ
##- MatrixMatrixMultiply[R](A,B)
##- MatrixVectorMultiply[R](A,v)
##
##PARAMETERS
##- R     : the domain of computation
##- A,B   : matrices of values in R
##- v     : vector of values in R
##
##RETURNS
##
##- MatrixMatrixMultiply[R](A,B) returns a matrix over R, the matrix product A.B
##- MatrixVectorMultiply[R](A,v) returns a vector over R, the product A.v
##
##SYNOPSIS
##- The (indexed) parameter R, which specifies the domain, a commutative ring,
##  must be a Maple table (module) which has the following values (exports):
##
##  R[`0`] : a constant for the zero of the ring R
##  R[`1`] : a constant for the (multiplicative) identity of R
##  R[`+`] : a procedure for adding elements of R (nary)
##  R[`-`] : a procedure for negating and subtracting elements of R (unary and binary)
##  R[`*`] : a procedure for multiplying elements of R (binary and commutative)
##  R[`=`] : a boolean procedure for testing if two elements of R are equal
## 
##- The parameters A, B, and v must have compatible dimensions for the product.
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Z[`0`],Z[`1`],Z[`+`],Z[`-`],Z[`*`],Z[`=`]) := (0,1,`+`,`-`,`*`,`=`);
##
##             Z[0], Z[1], Z[+], Z[-], Z[*], Z[=] := 0, 1, +, -, *, =
## 
##> A := Matrix([[2,1,4],[3,2,1],[0,0,5]]);
##                                    [2    1    4]
##                                    [           ]
##                               A := [3    2    1]
##                                    [           ]
##                                    [0    0    5]
## 
##> B := Matrix([[1,2,3],[2,1,2],[3,2,1]]);
##                                    [1    2    3]
##                                    [           ]
##                               B := [2    1    2]
##                                    [           ]
##                                    [3    2    1]
## 
##> MatrixMatrixMultiply[Z](A,B);
##                                [16    13    12]
##                                [              ]
##                                [10    10    14]
##                                [              ]
##                                [15    10     5]
## 
##> v := Vector([1,2,3]);
##                                         [1]
##                                         [ ]
##                                    v := [2]
##                                         [ ]
##                                         [3]
## 
##> MatrixVectorMultiply[Z](A,v);
##                                      [16]
##                                      [  ]
##                                      [10]
##                                      [  ]
##                                      [15]
##

MatrixMatrixMultiply := proc(A::Matrix,B::Matrix) local D,n,p,m,C,i,j,k;
  D := GenericCheck( procname, MatrixMatrixMultiplyOperations );
  if op(1,A)[2]<>op(1,B)[1] then error 
     "first matrix column dimension (%1) <> second matrix row dimension (%2)", op(1,A)[2], op(1,B)[1]; fi;
  n,p := op(1,A);
  m := op(1,B)[2];
  C := Matrix(n,m);
  for i to n do for j to m do C[i,j] := D[`+`](seq(D[`*`](A[i,k],B[k,j]),k=1..p)) od od;
  C
end:

MatrixVectorMultiply := proc(A::Matrix,v::Vector) local D,n,p,m,C,i,k;
  D := GenericCheck( procname, MatrixMatrixMultiplyOperations );
  n,p := op(1,A);
  m := op(1,v);
  if p <> m then error "vector dimension (%1) must be the same as the matrix column dimension (%2)", m,p; fi; 
  C := Vector(n);
  for i to n do C[i] := D[`+`](seq(D[`*`](A[i,k],v[k]),k=1..p)) od;
  C
end:

##CALLINGSEQ
## - BareissAlgorithm[D](A)
## - BareissAlgorithm[D](A,'r','d')
##
##PARAMETERS
## - D     : the domain of computation
## - A     : rectangular matrix of values in D
## - r     : name
## - d     : name
##
##RETURNS
##
## - BareissAlgorithm[D](A) returns a Matrix of values in D.
## - If r is specified, it is assigned an integer, the rank of A.
## - If d is specified, and A is square, it is assigned the determinant of A.
##
##SYNOPSIS
## - The (indexed) parameter D, which specifies the domain, an integral domain,
##   a commutative ring with exact division.  It must be a Maple table (module)
##   which has the following values (exports):
##
##   D[`0`] : a constant for the zero of the ring R
##   D[`1`] : a constant for the (multiplicative) identity of R
##   D[`+`] : a procedure for adding elements of R (nary)
##   D[`-`] : a procedure for negating and subtracting elements of R (unary and binary)
##   D[`*`] : a procedure for multiplying elements of R (binary and commutative)
##   D[`=`] : a boolean procedure for testing if two elements of R are equal
##   D[Divide] : a boolean procedure for testing if a | b and if so assigns q the
##               quotient of a divided by b.
## 
## - BareissAlgorithm[D](A) runs Bareiss' fraction-free row reduction
##   on a copy of A.  The output matrix B is upper triangular.  The entry B[i,i] is
##   the determinant of the principal i by i submatrix of A.  Thus if A
##   is a square of dimension n, thus B[n,n] is the determinant of A up to a unit.
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Z[`0`],Z[`1`],Z[`+`],Z[`-`],Z[`*`],Z[`=`]) := (0,1,`+`,`-`,`*`,`=`):
##> Z[Divide] := proc(a,b,q) evalb( irem(args) = 0 ) end:
##> A := Matrix([[3,4,5,7],[5,7,11,13],[7,11,13,17]]);
##                                [3     4     5     7]
##                                [                   ]
##                           A := [5     7    11    13]
##                                [                   ]
##                                [7    11    13    17]
##
##> BareissAlgorithm[Z](A,'r');
##                              [3    4      5     7]
##                              [                   ]
##                              [0    1      8     4]
##                              [                   ]
##                              [0    0    -12    -6]
##
##> r;
##                                        3
##
##

BareissAlgorithm := proc(B::Matrix,rank::name,det::name)
local D,A,n,m,i,j,c,r,divisor,s,zero,one,q;
    userinfo(2,procname, sprintf("Applying Fraction Free Gaussian Elimination"));
    D := GenericCheck( procname, BareissAlgorithmOperations );
    A := Matrix(B);
    m,n := LinearAlgebra:-Dimensions(A);

    if nargs > 2 and n <> m then error "cannot compute determinant of a non-square matrix" fi;

    zero := D[`0`];
    one := D[`1`];
    s := one;
    divisor := one;

    r := 1;
    for c to n while r <= m do
        # find pivot
        for i from r to m while D[`=`](A[i,c],zero) do od;
        if i > n or i > m then s := zero; next fi;

        userinfo(2,procname, sprintf("elimination at row %d",c));
        sprintf("elimination at row %d",c);

        if i <> r and i <= m then
            # interchange row i with row r
            # to make A[r,c] the pivot
            s := D[`-`](s);
            for j from c to n do A[i,j],A[r,j] := A[r,j],A[i,j] od
        fi;

        for i from r+1 to m do
            for j from c+1 to n do
                A[i,j] := D[`-`]( D[`*`](A[r,c],A[i,j]), D[`*`](A[i,c],A[r,j]) );
                    if not D[`=`](divisor,one) then
                    if not D[Divide](A[i,j],divisor,'q') then
error "Divide routine failed on exact division of %1 by %2", A[i,j], divisor;
                    end if;
                    A[i,j] := q;
                    fi;
            od;
            A[i,c] := zero;
        od;
        divisor := A[r,c];
        r := r+1   # go to next row

    od;  # go to next column

    if nargs>1 then rank := r-1 fi;
    if nargs>2 then det := D[`*`](s,A[n,n]) fi;
    A
end:

## CALLINGSEQ
##- HessenbergForm[F](A)
##  HessenbergForm[F](A,output=out)
##
##PARAMETERS
##- F     : a table or module, the domain of computation, a field
##- A     : square matrix of values in F
##- out   : one of 'H', 'U' or a list containing one or more of these names
##
##RETURNS
##
##- HessenbergForm[F](A) returns a square matrix H of values in F,
##  the upper Hessenberg form of A.
##
##- HermiteForm[E](A,output=['H','U']) returns the matrix H and
##  also the multiplier matrix U satisfying H = U A U^(-1) .
##
##SYNOPSIS
##- HessenbergForm[F](A) returns the upper Hessenberg form H of A
##
##- Given an n by n matrix A of elements in F, a field,
##  the algorithm converts a copy of A into upper Hessenberg form H using O(n^3)
##  operations in F.  The algorithm requires that F be a field and should only
##  be used if F is finite as there is a severe expression swell in computing H.
##
##- The (indexed) parameter F, which specifies the domain of computation, a field,
##  must be a Maple table (or module) which has the following values (exports):
##
##  F[`0`]: a constant for the zero of the ring F
##  F[`1`]: a constant for the (multiplicative) identity of F
##  F[`+`]: a procedure for adding elements of F (nary)
##  F[`-`]: a procedure for negating and subtracting elements of F (unary and binary)
##  F[`*`]: a procedure for multiplying two elements of F (commutative)
##  F[`/`]: a procedure for dividing two elements of F
##  F[`=`]: a boolean procedure for testing if two elements in F are equal
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Q[`0`],Q[`1`],Q[`+`],Q[`-`],Q[`*`],Q[`/`],Q[`=`]) := (0,1,`+`,`-`,`*`,`/`,`=`):
##> A := Matrix([[2,-7,-3,4],[1,-3,-4,5],[-7,10,5,-7],[-7,10,5,-7]]);
###                                       [ 2    -7    -3     4]
###                                       [                    ]
###                                       [ 1    -3    -4     5]
###                                  A := [                    ]
###                                       [-7    10     5    -7]
###                                       [                    ]
###                                       [-7    10     5    -7]
##
##> H := HessenbergForm[Q](A);
##< Matrix([[2,-14,1,4], [1,-10,1,5], [0,-46,5,28], [0,0,0,0]]);
###                             [2    -14    1     4]
###                             [                   ]
###                             [1    -10    1     5]
###                        H := [                   ]
###                             [0    -46    5    28]
###                             [                   ]
###                             [0      0    0     0]
##
##
##> H,U := HessenbergForm[Q](A,output=['H','U']);
###                        [2    -14    1     4]  [1    0     0    0]
###                        [                   ]  [                 ]
###                        [1    -10    1     5]  [0    1     0    0]
###                H, U := [                   ], [                 ]
###                        [0    -46    5    28]  [0    7     1    0]
###                        [                   ]  [                 ]
###                        [0      0    0     0]  [0    0    -1    1]
##
##> MatrixMatrixMultiply[Q](MatrixMatrixMultiply[Q](U,A),MatrixInverse[Q](U));
##< H;
###                           [2    -14    1     4]
###                           [                   ]
###                           [1    -10    1     5]
###                           [                   ]
###                           [0    -46    5    28]
###                           [                   ]
###                           [0      0    0     0]
##
##

HessenbergForm := proc(A::Matrix,out::{name,
    identical(output)={identical(U),identical(H),list({identical(U),identical(H)})}})
local F,rows,n,B,m,one,zero,t,t2,u,i,j,n2,V;
  F := GenericCheck( procname, HessenbergFormOperations );
  n2 := evalb(nargs>=2);
  B := Matrix(A);
  rows,n := LinearAlgebra:-Dimensions(B);
  if rows<>n then error "Matrix must be square"; fi;

  one := F[`1`];
  zero := F[`0`];

  if n2 then
    V := Matrix(n,n,'fill'=zero);
    for i to n do V[i,i] := one od;
  fi;

  for m from 2 to n-1 do
    if not F[`=`](B[m,m-1],zero) then
      t := B[m,m-1];
    else
      for i from m to n while F[`=`](B[i,m-1],zero) do od;
      if i > n then next fi;
      t := B[i,m-1]; #pivot

      # swap row i and row m
      for j from m-1 to n do t2:=B[i,j]; B[i,j]:=B[m,j]; B[m,j]:=t2 od;

      if n2 then
        for j to n do t2:=V[i,j]; V[i,j]:=V[m,j]; V[m,j]:=t2 od;
      fi;

      # swap column i and column m
      for j to n do t2:=B[j,i]; B[j,i]:=B[j,m]; B[j,m]:=t2 od;

    fi;

    # eliminate
    for i from m+1 to n do
      if not F[`=`](B[i,m-1],zero) then
        u := F[`/`](B[i,m-1],t);
        for j from m to n do
          B[i,j] := F[`-`](B[i,j],F[`*`](u,B[m,j]));
        od;
        B[i,m-1] := zero;

        if n2 then
          for j to n do V[i,j] := F[`-`](V[i,j],F[`*`](u,V[m,j])) od;
        fi;

        # set column m to column m + u*column i
        for j to n do
          B[j,m] := F[`+`](B[j,m],F[`*`](u,B[j,i]));
        od;

      fi;
    od;
  od;
  if nargs=1 then return B fi;
  if type(out,name) then out := V; return B fi;
  B := subs( {'H'=B,'U'=V}, rhs(out) );
  if type(rhs(out),list) then op(B) else B fi;
end:

## CALLINGSEQ
##- HessenbergAlgorithm[F](A)
##
##PARAMETERS
##- F     : the domain of computation, a field
##- A     : square matrix of values in F
##
##RETURNS
##
##- HessenbergAlgorithm[F](A) returns a vector of values from F encoding
##  the characteristic polynomial of A.
##
##SYNOPSIS
##- Given an n by n matrix A of elements in F, a field, 
##  HessenbergAlgorithm[F](A) returns a Vector V of n+1 values from F encoding
##  the characteristic polynomial of A as 
##
##     V[1] x^n + V[2] x^(n-1) + .... + V[n] x + V[n+1]
##
##- The algorithm converts a copy of A into upper Hessenberg form H using O(n^3)
##  operations in F then expands the determinant of x I - H in a further O(n^3)
##  operations in F.  The algorithm requires that F be a field and should only
##  be used if F is finite as there is a severe expression swell in computing H.
##
##- The (indexed) parameter F, which specifies the domain of computation, a field,
##  must be a Maple table (or module) which has the following values (exports):
##
##  F[`0`]: a constant for the zero of the ring F
##  F[`1`]: a constant for the (multiplicative) identity of F
##  F[`+`]: a procedure for adding elements of F (nary)
##  F[`-`]: a procedure for negating and subtracting elements of F (unary and binary)
##  F[`*`]: a procedure for multiplying two elements of F (commutative)
##  F[`/`]: a procedure for dividing two elements of F
##  F[`=`]: a boolean procedure for testing if two elements in F are equal
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Q[`0`],Q[`1`],Q[`+`],Q[`-`],Q[`*`],Q[`/`],Q[`=`]) := (0,1,`+`,`-`,`*`,`/`,`=`):
##> A := Matrix([[2,1,4],[3,2,1],[0,0,5]]);
##
##                                   [2    1    4]
##                                   [           ]
##                              A := [3    2    1]
##                                   [           ]
##                                   [0    0    5]
##
##> C := HessenbergAlgorithm[Q](A);
##                                       [ 1]
##                                       [  ]
##                                       [-9]
##                                  C := [  ]
##                                       [21]
##                                       [  ]
##                                       [-5]
##
##> add(C[i+1]*x^(3-i),i=0..3);
##                                  3      2
##                            -5 + x  - 9 x  + 21 x
##

HessenbergAlgorithm := proc(A::Matrix)
local F,H,p,m,n,t,s,i,j,one,zero;

  F := GenericCheck( procname, FieldOperations );
  one,zero := F[`1`],F[`0`];
  H := HessenbergForm[F](A);
  p[0] := Vector([one]);
  m,n := LinearAlgebra:-Dimensions(H);
  for m to n do
    p[m] := Vector(m+1);
    p[m][1] := p[m-1][1];
    for j from 2 to m do
      p[m][j] := F[`-`](p[m-1][j],F[`*`](H[m,m],p[m-1][j-1]));
    od;
    p[m][m+1] := F[`-`](F[`*`](H[m,m],p[m-1][m]));
    t := F[`1`];
    for i to m-1 do
      t := F[`*`](t,H[m-i+1,m-i]);
      s := F[`*`](t,H[m-i,m]);
      for j to m-i do
        p[m][m-j+2] := F[`-`](p[m][m-j+2],F[`*`](s,p[m-i-1][m-i-j+1]));
      od;
    od;
  od;
  p[n];
end:

## CALLINGSEQ
##- GaussianElimination[F](A)
##- GaussianElimination[F](A,'r','d')
##- ReducedRowEchelonForm[F](A)
##- ReducedRowEchelonForm[F](A,'r','d')
##- ReducedRowEchelonForm[F](A,method=BareissAlgorithm)
##- ReducedRowEchelonForm[F](A,method=GaussianElimination)
##- RREF[F](A)
##- RREF[F](A,'r','d')
##- RREF[F](A,method=BareissAlgorithm)
##- RREF[F](A,method=GaussianElimination)
##
##PARAMETERS
##- F     : the domain of computation, a field
##- A     : rectangular matrix over values in F
##- r     : name
##- d     : name
##
##RETURNS
##
##- A matrix of values in F, the reduced row Echelon form of the matrix A.
##- (optionally) assigns r the rank of A, a non-negative integer.
##- (optionally) assigns d the determinant of A, an element of F.
##
##SYNOPSIS
##- GaussianElimination[F](A) makes a copy of the matrix A and reduces it
##  to row Echelon form (upper triangular form) with leading 1's.
##
##- ReducedRowEchelonForm[F](A) makes a copy of the matrix A and reduces it
##  to reduced row Echelon form.
##
##- RREF is an abbreviation for ReducedRowEchelonForm
##
##- The (indexed) parameter F, which specifies the domain of computation, a field,
##  must be a Maple table (or module) which has the following values (exports):
##
##  F[`0`]: a constant for the zero of the ring F
##  F[`1`]: a constant for the (multiplicative) identity of F
##  F[`+`]: a procedure for adding elements of F (nary)
##  F[`-`]: a procedure for negating and subtracting elements of F (unary and binary)
##  F[`*`]: a procedure for multiplying two elements of F (commutative)
##  F[`/`]: a procedure for dividing two elements of F
##  F[`=`]: a boolean procedure for testing if two elements in F are equal
##
##- ReducedRowEchelonForm can use either GaussianElimination or the Bareiss algorithm
##  to reduce the system to triangular form.  If the Bareiss algorithm is used, 
##  the leading entries of each row are normalized to one as back substitution 
##  is performed, which avoids normalizing entries which are eliminated during
##  back substitution.
##
##  The Bareiss algorithm requires the field to support exact division, 
##  i.e., it requires F to be an integral domain with the following operation:
##                                  
##    F[Divide]: a boolean procedure for dividing two elements of F where
##    F[Divide](a,b,'q') outputs true if b|a and optionally assigns q
##       the quotient such that a=bq.
##                                  
##- If the method is not given and the operation F[Divide] is defined, then
##  the Bareiss algorithm is used, otherwise GaussianElimination is used.
##
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Q[`0`],Q[`1`],Q[`+`],Q[`-`],Q[`*`],Q[`/`],Q[`=`]) := (0,1,`+`,`-`,`*`,`/`,`=`);
##
##         Q[0], Q[1], Q[+], Q[-], Q[*], Q[/], Q[=] := 0, 1, +, -, *, /, =
##
##> A := Matrix([[1,2,3],[0,0,0],[3,2,1]]);
##                                    [1    2    3]
##                                    [           ]
##                               A := [0    0    0]
##                                    [           ]
##                                    [3    2    1]
## 
##
##> GaussianElimination[Q](A);
##                                 [1    2    3]
##                                 [           ]
##                                 [0    1    2]
##                                 [           ]
##                                 [0    0    0]
##
##> ReducedRowEchelonForm[Q](A,'r','d');
##
##                                [1    0    -1]
##                                [            ]
##                                [0    1     2]
##                                [            ]
##                                [0    0     0]
##
##> r,d;
##                                     2, 0
##
##> A := Matrix([[1,2,1,0],[2,1,0,1]]);
##
##                                 [1    2    1    0]
##                            A := [                ]
##                                 [2    1    0    1]
##
##
##> B := GaussianElimination[Q](A);
##
##                              [1    2     1      0  ]
##                         B := [                     ]
##                              [0    1    2/3    -1/3]
##
##> RREF[Q](B);
##
##                           [1    0    -1/3    2/3 ]
##                           [                      ]
##                           [0    1    2/3     -1/3]
##

GaussianElimination := proc(B::Matrix,rank::name,det::name)
local F,d,i,j,k,c,m,n,r,s,t,A;
    F := GenericCheck( procname, GaussianEliminationOperations );
    n,m := LinearAlgebra:-Dimensions(B);

    if nargs > 2 and n <> m then error "cannot compute determinant of a non-square matrix" fi;

    A := Matrix(B); # makes a copy of B note

    d := F[`1`];
    for i to n do
        for j to m while F[`=`](A[i,j],F[`0`]) do od;
        if j > m or F[`=`](A[i,j],F[`1`]) then next fi;
        d := F[`*`](d,A[i,j]);
        s := F[`/`](F[`1`],A[i,j]);
        for k from j+1 to m do A[i,k] := F[`*`](s,A[i,k]) od;
        A[i,j] := F[`1`];
    od;

    r := 1;

    for c to m while r <= n do

        for i from r to n while F[`=`](A[i,c],F[`0`]) do od;
        if i > n then d := F[`0`]; next fi;

        if i <> r then
        d := F[`-`](d);
        # interchange row i with row r
        for j from c to m do t := A[i,j]; A[i,j] := A[r,j]; A[r,j] := t od
        fi;

        for i from r+1 to n do
            if F[`=`](A[i,c],F[`0`]) then next fi;
            A[i,c] := F[`0`];
            for j from c+1 to m do A[i,j] := F[`-`](A[i,j],A[r,j]) od;
            for j from c+1 to m while F[`=`](A[i,j],F[`0`]) do od;
            if j > m then next fi;
            d := F[`*`](A[i,j],d);
            s := F[`/`](F[`1`],A[i,j]);
            for k from j+1 to m do A[i,k] := F[`*`](s,A[i,k]) od;
            A[i,j] := F[`1`];
        od;

        r := r + 1      # go to next row

    od;         # go to next column

    if nargs>1 then rank := r-1 fi;
    if nargs>2 then det := d fi;
    A

end:

ReducedRowEchelonForm := proc(B::Matrix,rank::{name,equation},det::{name,equation})
local F,i,j,c,m,n,r,A,alg,opts;  
    opts := select(type, [args[2..nargs]], 'equation');
    hasoption(opts,'method'={identical(GaussianElimination),identical('BareissAlgorithm')},'alg','opts');
    if opts<>[] then error "unrecognized option(s): %1", opts fi;

    F := GenericCheck( procname, ReducedRowEchelonFormOperations );
    n,m := LinearAlgebra:-Dimensions(B);           
    if not assigned(alg) then
	alg := `if`(HasOperation(F, Divide), BareissAlgorithm, GaussianElimination)
    end if;

    if alg=GaussianElimination then 
	    
    A := GaussianElimination[F](op(remove(type, [args], equation)));
    r := 1;
    for c to m while r <= n do

       	for i from r to n while F[`=`](A[i,c],F[`0`]) do od;
        if i > n then next fi;
        for i to r-1 do
            if F[`=`](A[i,c],F[`0`]) then next fi;
            for j from c+1 to m do
                A[i,j] := F[`-`](A[i,j],F[`*`](A[i,c],A[r,j]))
            od;
            A[i,c] := F[`0`]
       	od;
        r := r + 1      # go to next row

    od;         # go to next column

    else

    A := BareissAlgorithm[F](op(remove(type, [args], equation)));
    for r from n to 1 by -1 do
	for c from min(r,m) to m while F[`=`](A[r,c],F[`0`]) do od;
	if c > m then next end if;
	for j from c+1 to m do A[r,j] := F[`/`](A[r,j],A[r,c]) od;
	A[r,c] := F[`1`];
	for i to r-1 do for j from c+1 to m do 
		A[i,j] := F[`-`](A[i,j], F[`*`](A[i,c], A[r,j])) 
        od; A[i,c] := F[`0`] od;
    od;

    fi;
    A
end:

RREF := ReducedRowEchelonForm;

## CALLINGSEQ
##- MatrixInverse[F](A)
##
##PARAMETERS
##- F     : the domain of computation, a field
##- A     : rectangular matrix over values in F
##
##RETURNS
##
##- A square matrix of values in F, the inverse of the matrix A.
##
##SYNOPSIS
##- MatrixInverse(A) computes the matrix inverse of the matrix A over the field F.
##
##- The (indexed) parameter F, which specifies the domain of computation, a field,
##  must be a Maple table (or module) which has the following values (exports):
##
##  F[`0`]: a constant for the zero of the ring F
##  F[`1`]: a constant for the (multiplicative) identity of F
##  F[`+`]: a procedure for adding elements of F (nary)
##  F[`-`]: a procedure for negating and subtracting elements of F (unary and binary)
##  F[`*`]: a procedure for multiplying two elements of F (commutative)
##  F[`/`]: a procedure for dividing two elements of F
##  F[`=`]: a boolean procedure for testing if two elements in F are equal
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Q[`0`],Q[`1`],Q[`+`],Q[`-`],Q[`*`],Q[`/`],Q[`=`]) := (0,1,`+`,`-`,`*`,`/`,`=`);
##
##         Q[0], Q[1], Q[+], Q[-], Q[*], Q[/], Q[=] := 0, 1, +, -, *, /, =
##
##> A := Matrix([[1,2,3],[2,1,2],[3,2,1]]);
##                                    [1    2    3]
##                                    [           ]
##                               A := [2    1    2]
##                                    [           ]
##                                    [3    2    1]
## 
##> MatrixInverse[Q](A);
##                              [-3/8    1/2    1/8 ]
##                              [                   ]
##                              [1/2     -1     1/2 ]
##                              [                   ]
##                              [1/8     1/2    -3/8]
##

MatrixInverse := proc(A::Matrix) local F,m,n,C,B,zero,one,i;
  F := GenericCheck( procname, MatrixInverseOperations );
  m,n := LinearAlgebra:-Dimensions(A);
  if m<>n then error "Matrix must be square" fi;
  zero := F[`0`];
  one := F[`1`];
  C := Matrix(n,2*n,A,'fill'=zero);
  for i to n do
    C[i,n+i] := one;
  od;
  B := ReducedRowEchelonForm[F](C);
  if F[`=`](B[n,n],zero) then error "singular matrix" fi;
  B[1..n,n+1..2*n]

end:

## CALLINGSEQ
##- NullSpace[F](A)
##
##PARAMETERS
##- F     : the domain of computation, a field
##- A     : rectangular matrix over values in F
##
##RETURNS
##
##- A set B of vectors of values in F, the basis for the linear system A x = 0.
##
##SYNOPSIS
##- NullSpace(A) returns a basis for the linear system A x = 0 over the field F
##  as a set of vectors B = [b1, b2, ...].
##
##- The (indexed) parameter F, which specifies the domain of computation, a field,
##  must be a Maple table (or module) which has the following values (exports):
##
##  F[`0`]: a constant for the zero of the ring F
##  F[`1`]: a constant for the (multiplicative) identity of F
##  F[`+`]: a procedure for adding elements of F (nary)
##  F[`-`]: a procedure for negating and subtracting elements of F (unary and binary)
##  F[`*`]: a procedure for multiplying two elements of F (commutative)
##  F[`/`]: a procedure for dividing two elements of F
##  F[`=`]: a boolean procedure for testing if two elements in F are equal
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Q[`0`],Q[`1`],Q[`+`],Q[`-`],Q[`*`],Q[`/`],Q[`=`]) := (0,1,`+`,`-`,`*`,`/`,`=`);
##
##         Q[0], Q[1], Q[+], Q[-], Q[*], Q[/], Q[=] := 0, 1, +, -, *, /, =
##
##> A := Matrix([[1,2,3],[1,3,5],[0,1,2]]);
##                                    [1    2    3]
##                                    [           ]
##                               A := [1    3    5]
##                                    [           ]
##                                    [0    1    2]
## 
##>  NullSpace[Q](A);
##                                      [ 1]
##                                      [  ]
##                                     {[-2]}
##                                      [  ]
##                                      [ 1]
## 
##> A := Matrix([[1,2,3],[2,4,6],[-1,-2,-3]]);
##                                   [ 1     2     3]
##                                   [              ]
##                              A := [ 2     4     6]
##                                   [              ]
##                                   [-1    -2    -3]
## 
##> NullSpace[Q](A);
##                                   [-3]  [-2]
##                                   [  ]  [  ]
##                                  {[ 0], [ 1]}
##                                   [  ]  [  ]
##                                   [ 1]  [ 0]
##                                        2
## 

NullSpace := proc(B::Matrix,nullity::name)
local F,A,N,l,m,n,i,j,r,s,t,u,v,k;
    F := GenericCheck( procname, NullSpaceOperations );
    A := ReducedRowEchelonForm[F](B,'r');
    l,m := LinearAlgebra:-Dimensions(A);
    n := m-r;
    if nargs > 1 then nullity := n fi; # not documented
    if n=0 then return  {}  fi;

    if r > 0 then s := array(1..r) fi;
    u := array([seq(k+r,k=1..n)]);
    v := array([seq(r+1,k=1..n)]);
    # u is a vector of column pointers representing ``free'' variables.
    #   initially set to the last n columns.
    # v is a vector of ``nonfree'' variables lying in front of the
    #   corresponding free variable in u - initially set to be the first
    #   n rows
    j := 1;
    for i to l while j <= m do
    while j <= m and F[`=`](A[i,j],F[`0`]) do
        u[j-i+1] := j;
        v[j-i+1] := i;
        j := j+1
    od;
    if i <= r then s[i] := j fi;
    j := j+1
    od;

    N := array(1..n); t := array(1..m);
    for i to n do
      # N[i], the i'th nullspace vector, is obtained from col(M,u[i])
      for j to m do t[j] := F[`0`] od;
      t[u[i]] := F[`1`];
      for j to v[i]-1 do t[s[j]] := F[`-`](A[j,u[i]]) od;
        N[i] := Vector['column'](t);
    od;

    { seq(N[i], i=1..n) }

end:

## CALLINGSEQ
##- LinearSolve[F](A,b)
##- LinearSolve[F](A,b,...)
##
##PARAMETERS
##- F     : the domain of computation, a field
##- A     : rectangular matrix over values in F
##- b     : vector or matrix of values in F
##- ...   : options
##
##RETURNS
##
##- The return values are controlled by the output option which is described
##  below.  By default, if the linear system A x = b is consistent, the output
##  is a pair (x, B) where x is a vector, a particular solution of A x = b,
##  and B is a list of vectors, a basis for the solutions of A x = 0.  If the
##  linear system A x = b is inconsistent, the error "inconsistent system" is
##  generated.
##
##- Note, the default output format for the solutions returned differs
##  from the LinearSolve command in the LinearAlgebra package which returns
##  the solutions in terms of free parameters.
##
##SYNOPSIS
##- The (indexed) parameter F, which specifies the domain of computation, a field,
##  must be a Maple table (or module) which has the following values (exports):
##
##  F[`0`]: a constant for the zero of the ring F
##  F[`1`]: a constant for the (multiplicative) identity of F
##  F[`+`]: a procedure for adding elements of F (nary)
##  F[`-`]: a procedure for negating and subtracting elements of F (unary and binary)
##  F[`*`]: a procedure for multiplying two elements of F (commutative)
##  F[`/`]: a procedure for dividing two elements of F
##  F[`=`]: a boolean procedure for testing if two elements in F are equal
##
##- If the linear system A x = b is consistent, LinearSolve[F](A,b) returns (v,B)
##  where v is Maple vector and B = [b1,b2,...,] is a list of vectors.  The solutions
##  of the system are the vectors { x + a1 b1 + a2 b2 + ... } for a1, a2, ... in F.
##  Thus v is a particular solution and B is a basis for the solutions of A x = 0.
##  If the dimension of the solution space is 0 then B will be the empty list.
##
##- If the optional argument output=[...] is specified, it specifies what values
##  are returned and in what order.  The keywords in the output options may
##  be any of 'solution', 'basis', or 'dimension', in any order.
##  The default output format corresponds to output=[solution,basis] meaning
##  a particular solution and a basis for the solutions of A x = b is output.
##  If output=[solution] is specified, the output is a single vector of solutions
##  in terms of parameters.  The parameter names may be specified by the optional
##  argument free=t described below.  By default, the names _t[1], _t[2], ... are used.
##
##- (optionally) if free=t is specified, where t is a symbol or list of names,
##  the solution(s) are returned as a single vector of values parametrized by
##  t[1], t[2], ..., t[d].  Note, this option is only available when the
##  output=[solution] option is also specified.
##  
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Q[`0`],Q[`1`],Q[`+`],Q[`-`],Q[`*`],Q[`/`],Q[`=`]) :=
##  (0,1,`+`,`-`,`*`,`/`,`=`);
###        Q[0], Q[1], Q[+], Q[-], Q[*], Q[/], Q[=] := 0, 1, +, -, *, /, =
###
##> A,b := Matrix([[1,2,3],[1,0,1],[0,1,2]]), <1,2,1>;
###                                  [1    2    3]  [1]
###                                  [           ]  [ ]
###                          A, b := [1    0    1], [2]
###                                  [           ]  [ ]
###                                  [0    1    2]  [1]
###
##> x,B := LinearSolve[Q](A,b);
##< <1/2,-2,3/2>, [];
###                                       [1/2]
###                                       [   ]
###                               x, B := [-2 ], []
###                                       [   ]
###                                       [3/2]
###
##> x := LinearSolve[Q](A,b,output=[solution, dimension]);
##< <1/2,-2,3/2>, 0;
###                                     [1/2]
###                                     [   ]
###                                x := [-2 ], 0
###                                     [   ]
###                                     [3/2]
###
###
##> MatrixVectorMultiply[Q](A,x) = b;
##< <1,2,1> = <1,2,1>;
###                                   [1]   [1]
###                                   [ ]   [ ]
###                                   [2] = [2]
###                                   [ ]   [ ]
###                                   [1]   [1]
###
##> for i from 1 to 3 do A[2,i] := A[1,i]+A[3,i] od: b[2] := b[1]+b[3]:
##> A,b;
###                              [1    2    3]  [1]
###                              [           ]  [ ]
###                              [1    3    5], [2]
###                              [           ]  [ ]
###                              [0    1    2]  [1]
###
###
##> x,B := LinearSolve[Q](A,b);
##< <-1,1,0>, [<1,-2,1>];
###                                     [-1]   [ 1]
###                                     [  ]   [  ]
###                             x, B := [ 1], [[-2]]
###                                     [  ]   [  ]
###                                     [ 0]   [ 1]
###
##> x := x + t*B[1]; # symbolic solution
##< <t-1,1-2*t,t>;
###                                     [-1 + t ]
###                                     [       ]
###                                x := [1 - 2 t]
###                                     [       ]
###                                     [   t   ]
###
##> x,d := LinearSolve[Q](A,b,output=[solution,dimension],free=t);
##< <t[1]-1,1-2*t[1],t[1]>, 1;
###                                     [-1 + t[1] ]
###                                     [          ]
###                             x, d := [1 - 2 t[1]], 1
###                                     [          ]
###                                     [   t[1]   ]
###
##> A.x = b;
###                                   [1]   [1]
###                                   [ ]   [ ]
###                                   [2] = [2]
###                                   [ ]   [ ]
###                                   [1]   [1]
###

LinearSolve := proc(A::Matrix,b::{Matrix, Vector[column]})
local F,AA,out,m,n,rank,i,j,k,d,s,ns,V,G,opts,t,X,B;
  F := GenericCheck( procname, LinearSolveOperations );
  opts := [args[3..nargs]];
  hasoption(opts,'free={symbol,list(name)}','t','opts');
  out := ['solution','basis'];
  hasoption(opts,'output=list({identical(solution),identical(basis),
                               identical(dimension)})','out','opts');
  if opts<>[] then error "unrecognized option(s): %1", opts fi;
  m,n := LinearAlgebra:-Dimensions(A);
  d,s := op(1..2,[LinearAlgebra:-Dimensions(b),1]);
  if m <> d then
    error "number of rows of matrix, %1, does not match dimension of vector, %2", m, d;
  fi;
  AA := ReducedRowEchelonForm[F](Matrix([A,b]),'rank');
  for i from rank to n+s while F[`=`](AA[rank,i],F[`0`]) do od;
  if i > n then error "inconsistent system" fi;
  d := n-rank;
  if type(b,'Vector') then 
    for k from 0 to d do V[k]:=Vector(n,'fill'=F[`0`]) od;
    ns := n+1;
    s := NULL;
  else
    for k from 0 to d do V[k]:=Matrix(n,s,'fill'=F[`0`]) od;
    ns := n+1..n+s;
    s := 1..s:
  end if;
  k := 0;
  for i to n do
    if F[`=`](AA[i-k,i],F[`0`]) then
      k := k+1;
      for j to i-k do V[k][G[j],s] := F[`-`](AA[j,i]) od; 
      V[k][i,s] := F[`1`];
    else
      G[i-k] := i  
    fi;
  od;
  for j to n-k do V[0][G[j],s] := AA[j,ns] od;
  X,B := V[0], [seq(V[i],i=1..d)];
  if not assigned(t) and not has(out,'basis') then t := _t; fi;
  if assigned(t) then X := `+`( V[0], seq( B[i]*t[i],i=1..d ) ) fi;
  op( subs( {'solution'=X,'basis'=B,'dimension'=d}, out ) );
end:


## CALLINGSEQ
##- Determinant[R](A)
##- Determinant[R](A,method=BerkowitzAlgorithm)
##- Determinant[R](A,method=MinorExpansion)
##- Determinant[R](A,method=BareissAlgorithm)
##- Determinant[R](A,method=GaussianElimination)
##
##PARAMETERS
##- R     : the domain of computation
##- A     : square matrix of values in R
##
##RETURNS
##
##- Determinant[R](A) returns an element of R, the determinant of A.
##
##SYNOPSIS
##- The parameter A must be a square (n by n) matrix of values from R.
##
##- The (indexed) parameter R, which specifies the domain, a commutative ring,
##  must be a Maple table (module) which has the following values (exports):
##
##  R[`0`] : a constant for the zero of the ring R
##  R[`1`] : a constant for the (multiplicative) identity of R
##  R[`+`] : a procedure for adding elements of R (nary)
##  R[`-`] : a procedure for negating and subtracting elements of R (unary and binary)
##  R[`*`] : a procedure for multiplying elements of R (binary and commutative)
##  R[`=`] : a boolean procedure for testing if two elements of R are equal
## 
##- The optional argument method=... specifies the algorithm to be used.
##  The specific algorithms are listed below.
##
##  method=MinorExpansion directs the code to use minor expansion.
##    This algorithm uses O(n 2^n) arithmetic multiplications in R.
##
##  method=BerkowitzAlgorithm directs the code to use the Berkowitz
##    algorithm.  This algorithm uses O(n^4) arithmetic operations in R.
##
##  method=BareissAlgorithm directs the code to use the Bareiss algorithm.
##    This algorithm uses O(n^3) arithmetic operations in R but
##    requires exact division, i.e., it requires R to be an integral domain 
##    with the following operation defined:
##
##    R[Divide]: a boolean procedure for dividing two elements of R where
##    R[Divide](a,b,'q') outputs true if b|a and optionally assigns q
##       the quotient such that a=bq.
##
##  method=GaussianElimination directs the code to use the Gaussian
##    elimination algorithm.  This algorithm uses O(n^3) arithmetic 
##    operations in R but requires R to be a field, i.e., the
##    following operation must be defined:
##    R[`/`]: a procedure for dividing two elements of R
##
##  If the method is not given and the operation R[Divide] is defined,
##  then the Bareiss algorithm is used, otherwise if the operation R[`/`]
##  is defined then GaussianElimination is used, otherwise the Berkowitz 
##  algorithm is used.
##
##EXAMPLE
##> with(GenericLinearAlgebra):
##> (Z[`0`],Z[`1`],Z[`+`],Z[`-`],Z[`*`],Z[`=`]) := (0,1,`+`,`-`,`*`,`=`):
##> A := Matrix([[2,1,4],[3,2,1],[0,0,5]]);
##
##                                   [2    1    4]
##                                   [           ]
##                              A := [3    2    1]
##                                   [           ]
##                                   [0    0    5]
##
##> Determinant[Z](A);
##                                         5
##
##> (Q[`0`],Q[`1`],Q[`+`],Q[`-`],Q[`*`],Q[`/`],Q[`=`]) := (0,1,`+`,`-`,`*`,`/`,`=`):
##> A := Matrix([[2,1,4,6],[3,2,1,7],[0,0,5,1],[0,0,3,8]]);
##                                  [2    1    4    6]
##                                  [                ]
##                                  [3    2    1    7]
##                             A := [                ]
##                                  [0    0    5    1]
##                                  [                ]
##                                  [0    0    3    8]
##
##> Determinant[Q](A);
##                                         37
##
##> Determinant[Q](A,method=BerkowitzAlgorithm);
##                                         37
##

Determinant := proc(B::Matrix)
local D,A,opts,alg,m,n,L,d,r,det,C;
  
  opts := [args[2..nargs]];
  hasoption(opts,'method'={identical(BerkowitzAlgorithm),identical(GaussianElimination),
                           identical('BareissAlgorithm'),identical(MinorExpansion)},
      'alg','opts');
  if opts<>[] then error "unrecognized option(s): %1", opts fi;

  if alg=BerkowitzAlgorithm or alg=MinorExpansion then
    D := GenericCheck( procname, RingOperations );
  elif alg=BareissAlgorithm then
    D := GenericCheck( procname, DomainOperations );
  elif alg=GaussianElimination then
    D := GenericCheck( procname, FieldOperations );
  else
    D := GenericCheck( procname, RingOperations );
    if HasOperation(D,Divide) then alg := BareissAlgorithm;
    elif HasOperation(D,`/`) then alg := GaussianElimination;
    else alg := BerkowitzAlgorithm;
    fi;
  fi;
  
  m,n := LinearAlgebra:-Dimensions(B);
  if m<>n then error "Matrix must be square" fi;
  m,L := StronglyConnectedBlocks[D](B);
  if m>0 then return D[`0`] fi;
  det := D[`1`];
  for A in L while det <> D[`0`] do
    if alg=BerkowitzAlgorithm then 
       C := BerkowitzAlgorithm[D](A);
       n := LinearAlgebra:-Dimension(C)-1;
       C := C[n+1];
       if n mod 2 = 1 then C := D[`-`](C) fi;
       det := D[`*`](det,C);
    elif alg=MinorExpansion then
       det := D[`*`](det,MinorExpansion[D](A));
    elif alg=BareissAlgorithm then
       BareissAlgorithm[D](A,'r','d');
       det := D[`*`](det,d);
    else # alg = GaussianElimination
       GaussianElimination[D](A,'r','d');
       det := D[`*`](det,d);
    fi
  od;
  det;

end:

## CALLINGSEQ
##- CharacteristicPolynomial[R](A)
##- CharacteristicPolynomial[R](A,x)
##- CharacteristicPolynomial[R](A,output=factored)
##- CharacteristicPolynomial[R](A,output=expanded)
##- CharacteristicPolynomial[R](A,method=Berkowitz)
##- CharacteristicPolynomial[R](A,method=Hessenberg)
##
##PARAMETERS
##- R     : the domain of computation
##- x     : name of the variable
##- A     : square matrix of values in R
##
##RETURNS
##
##- CharacteristicPolynomial[R](A) or CharacteristicPolynomial[R](A,output=expanded)
##  returns a Vector of values from R, encoding the characteristic polynomial of A.
##- CharacteristicPolynomial[R](A,x) or CharacteristicPolynomial[R](A,x,output=expanded)
##  returns a Maple polynomial in x, in expanded form, with coefficients in R,
##  encoding the characteristic polynomial of A.
##- CharacteristicPolynomial[R](A,output=factored) returns a sequence of the form  
##  m, [v1, v2, ...] also encoding the characteristic polynomial of A.  Here m is a
##  non-negative integer and v1, v2, ... are vectors of values from R.
##- CharacteristicPolynomial[R](A,x,output=factored) returns a product of
##  Maple polynomials in x in with coefficients in R.
##
##SYNOPSIS
##- The (indexed) parameter R, which specifies the domain, a commutative ring,
##  must be a Maple table (module) which has the following values (exports):
##
##  R[`0`] : a constant for the zero of the ring R
##  R[`1`] : a constant for the (multiplicative) identity of R
##  R[`+`] : a procedure for adding elements of R (nary)
##  R[`-`] : a procedure for negating and subtracting elements of R (unary and binary)
##  R[`*`] : a procedure for multiplying elements of R (binary and commutative)
##  R[`=`] : a boolean procedure for testing if two elements of R are equal
## 
##- The parameter A must be a square (n by n) matrix of values from R.
##
##- The optional parameter x must be a name.
##
##- CharacteristicPolynomial[R](A) returns a Vector V of dimension n+1 of values in R containing
##  the coefficients of the characteristic polynomial of A.  The characteristic 
##  polynomial is the polynomial V[1]*x^n + V[2]*x^(n-1) + ... + V[n]*x + V[n+1].
##
##- CharacteristicPolynomial[R](A,x) returns the characteristic polynomial
##  as a Maple expression in the variable x.  This option should only be used
##  if the data type for R is compatible with Maple's * operator.  For example,
##  if the elements of R are represented by Vectors, or Arrays, then this 
##  option should not be used because Vector([1,2,3])*x is simplified 
##  to be Vector([x,2*x,3*x]).
##
##- The optional argument output=... specifies the form of the output.
##  In the case output=expanded, the characteristic polynomial is returned as
##  one vector encoding the characteristic polynomial in expanded form.
##  In the case output=factored, the characteristic polynomial is returned as
##  a sequence of the form m, [v1, v2, ...] where m is a non-negative
##  m is a non-negative integer, and the vectors v1, v2, ... are Vectors
##  of elements of R representing (not necessarily irreducible) factors of the
##  characteristic polynomial.  The integer m represents the factor x^m.  The 
##  implementation looks for diagonal blocks and computes the characteristic
##  polynomial of each block separately.
##
##- The optional argument method=... specifies the algorithm to be used.
##  The option method=Berkowitz directs the code to use the Berkowitz algorithm.
##  This algorithm uses O(n^4) arithmetic operations in R.
##  The option method=Hessenberg directs the code to use the Hessenberg algorithm.
##  This algorithm uses O(n^3) arithmetic operations in R but requires R to be
##  a field, i.e., the following operation must be defined:
##    R[`/`]: a procedure for dividing two elements of R
##  If method=... is not given, and the operation R[`/`] is defined, then the
##  Hessenberg algorithm is used, otherwise the Berkowitz algorithm is used.
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Z[`0`],Z[`1`],Z[`+`],Z[`-`],Z[`*`],Z[`=`]) := (0,1,`+`,`-`,`*`,`=`):
##> A := Matrix([[2,1,4],[3,2,1],[0,0,5]]);
##
##                                   [2    1    4]
##                                   [           ]
##                              A := [3    2    1]
##                                   [           ]
##                                   [0    0    5]
##
##> C := CharacteristicPolynomial[Z](A);
##                                       [ 1]
##                                       [  ]
##                                       [-9]
##                                  C := [  ]
##                                       [21]
##                                       [  ]
##                                       [-5]
##
##> add(C[i+1]*x^(3-i),i=0..3);
##                                  3      2
##                            -5 + x  - 9 x  + 21 x
##
##> C := CharacteristicPolynomial[Z](A,x);
##                                  3      2
##                            -5 + x  - 9 x  + 21 x
##
##> n,C := CharacteristicPolynomial[Z](A,output=factored);
##                                             [ 1]
##                                       [ 1]  [  ]
##                           n, C := 0, [[  ], [-4]]
##                                       [-5]  [  ]
##                                             [ 1]
##
##> x^n*(x+C[1][2])*(x^2+C[2][2]*x+C[2][3]);
##                                     2
##                           (x - 5) (x  - 4 x + 1)
##
##> CharacteristicPolynomial[Z](A,x,output=factored);
##                                     2
##                           (x - 5) (x  - 4 x + 1)
##
##> (Q[`0`],Q[`1`],Q[`+`],Q[`-`],Q[`*`],Q[`/`],Q[`=`]) := (0,1,`+`,`-`,`*`,`/`,`=`):
##
##> A:=Matrix([[2,-7,-3,4],[1,-3,-4,5],[0,0,5,-7],[0,0,0,0]]);
##                             [2    -7    -3     4]
##                             [                   ]
##                             [1    -3    -4     5]
##                        A := [                   ]
##                             [0     0     5    -7]
##                             [                   ]
##                             [0     0     0     0]
##
##> n,C := CharacteristicPolynomial[Q](A,output=factored);           
##                                        [1]
##                                  [ 1]  [ ]
##                              1, [[  ], [1]]
##                                  [-5]  [ ]
##                                        [1]
##
##> x^n*(x+C[1][2])*(x^2+C[2][2]*x+C[2][3]);
##                                      2
##                          x (x - 5) (x  + x + 1)
##
##> C := CharacteristicPolynomial[Q](A);                
##                                   [ 1]
##                                   [  ]
##                                   [-4]
##                                   [  ]
##                                   [-4]
##                                   [  ]
##                                   [-5]
##                                   [  ]
##                                   [ 0]
##
##> add(C[i+1]*x^(4-i),i=0..4);
##                           4      3      2
##                          x  - 4 x  - 4 x  - 5 x
##
##

CharacteristicPolynomial := proc(B::Matrix)
local x,D,A,L,V,ii,n,m,i,j,one,zero,MUL,RMUL,FAC,alg,out,opts;
  
  opts := [args[2..nargs]];
  if nargs>1 and type(args[2],name) then x := args[2]; opts := [args[3..nargs]]; fi;
  if hasoption(opts,'method'={identical('BerkowitzAlgorithm'),identical('HessenbergAlgorithm')},'alg','opts') then else alg := 'default'; fi;
  if hasoption(opts,'output'={identical('expanded'),identical('factored')},'out','opts') then else out := 'expanded'; fi;
  if opts<>[] then error "unrecognized option(s): %1", opts fi;

  if alg='HessenbergAlgorithm' then
    D := GenericCheck( procname, FieldOperations );
  elif alg='BerkowitzAlgorithm' then
    D := GenericCheck( procname, RingOperations );
  else
    D := GenericCheck( procname, RingOperations );
    alg := `if`( HasOperation(D,`/`),'HessenbergAlgorithm','BerkowitzAlgorithm');
  fi;
  
  m,n := LinearAlgebra:-Dimensions(B);
  if m<>n then error "Matrix must be square" fi;
  m,L := StronglyConnectedBlocks[D](B);
  one := D[`1`];
  zero := D[`0`];
  ii := 0;
  for A in L do
    ii := ii + 1;
    if alg=HessenbergAlgorithm then
      V[ii] := HessenbergAlgorithm[D](A)
    else
      V[ii] := BerkowitzAlgorithm[D](A)
    fi
  od;

  FAC := proc(V) local i,n;
         n := op(1,V);
         add( V[i]*x^(n-i), i=1..n );
  end:
  if out='factored' then
    if assigned(x) then 
         x^m*mul( FAC(V[j]), j=1..ii );
    else m, [seq(V[j],j=1..ii)];
    fi;
  else
    MUL := proc(A,B) local V,n,m,i,j;
      n,m := op(1,A),op(1,B);
      V := Vector(n+m-1,'fill'=zero);
      for i to n do
        for j to m do
          V[i+j-1] := D[`+`](V[i+j-1],D[`*`](A[i],B[j])); 
        od;
      od;
      V
    end;
    RMUL := proc(i,j)
      if i=j then V[i]
      elif i>j then Vector([one])
      else MUL(RMUL(i,iquo(i+j,2)),RMUL(iquo(i+j,2)+1,j))
      fi;
    end;
    V := Vector(op(1,B)[1]+1,RMUL(1,ii));
    if assigned(x) then FAC(V) else V fi;
  fi;
end:

## CALLINGSEQ
##- HermiteForm[E](B)
##- HermiteForm[E](B,output=out)
##
##PARAMETERS
##- E     : the domain of computation, an Euclidean domain
##- B     : m by n Matrix of values in E
##- out   : one of 'H', 'U' or a list containing one or more of these names
##
##RETURNS
##
##- Hermite[E](B) returns an m by n matrix H of values in E
##- HermiteForm[E](A,output=['H','U']) returns the matrix H
##  and also the multiplier matrix U, an m by m matrix of values in E,
##  satisfying U B = H .
##
##SYNOPSIS
##- Given an m by n matrix H of values in E, HermiteForm[E](B) returns the
##  Hermite form H of B, an m by n matrix of values in E.
##
##- The Hermite normal form matrix H satisfies:
##    (1) H is row-equivalent to B and H is in row-Echelon form
##    (2) The bottom-most nonzero entry p[j] = H[b,j] in each column j is unit normal,
##        and either H[i,j]=0 or the Euclidean norm of H[i,j] where i<b is less than Euclidean norm of p[j]
##    (3) If B is n x n square matrix, then prod(H[i,i],i=1..n) = u*det(B) where u is a unit in E  
##
##- The uniqueness of H depends on the uniqueness of the remainder operation in E.
##  For example, if E is the ring of integers, and a and b are integers, and the
##  remainder of a divided b is in the positive range 0..abs(b)-1, then H is unique.
##  If Maple's irem function is used, as in the example below, because the remainder
##  is in the range 1-abs(b)..abs(b)-1, H is not unique.
##   
##- The (indexed) parameter E, which specifies the domain of computation, a Euclidean
##  domain, must be a Maple table (or module) which has the following values (exports):
##
##  E[`0`]: a constant for the zero of the ring E
##  E[`1`]: a constant for the (multiplicative) identity of E
##  E[`+`]: a procedure for adding elements of E (nary)
##  E[`-`]: a procedure for negating and subtracting elements of E (unary and binary)
##  E[`*`]: a procedure for multiplying two elements of E (commutative)
##  E[`=`]: a boolean procedure for testing if two elements in F are equal
##  E[Quo]: a procedure which computes the quotient of a divided by b.
##          E[Quo](a,b,'r') computes the quotient q of a divided b and
##          optionally assigns r the remainder satisfying a = b q + r.
##  E[Rem]: a procedure for finding the remainder of a divided by b.
##          E[Rem(a,b,'q') computes the remainder r of a divided b and
##          optionally assigns q the quotient satisfying a = b q + r.
##  E[Gcdex]: a procedure for finding the gcd g of a anb b, an element of E.
##          E[Gcdex](a,b,'s','t') computes the gcd of a and b and
##          optionally assigns s and t elements of E satisfying s a + t b = g.
##  E[UnitPart]: a procedure for returning the unit part of an element in E
##  E[EuclideanNorm]: a procedure for computing the Euclidean norm of an
##          element in E, a non-negative integer.
##
## For a,b in E, b non-zero, the remainder r and quotient q satisfy
##          a = b q + r and r = 0 or N(r) < N(b) where N = EuclideanNorm.
## For non-zero a,b in E, units u,v in E, the Euclidean norm N satisfies
##          N(a b) >= N(a)
##          N(u) = N(v) and N(u a) = N(a)
##
##- The Hermite form is computed by putting the principal block H[1..i,1..i]
##  into Hermite form using elementary Row operations.  This algorithm does
##  at most O(n^4) operations in E.
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Z[`0`],Z[`1`],Z[`+`],Z[`-`],Z[`*`],Z[`=`]) := (0,1,`+`,`-`,`*`,`=`):
##> Z[Gcdex] := igcdex:
##> Z[Quo], Z[Rem] := iquo, irem:
##> Z[UnitPart] := sign:
##> Z[EuclideanNorm] := abs:
##> A:=Matrix([[1,2,3,4,5],[2,3,4,5,6],[4,1,-2,-5,-2],[-1,-4,-2,1,2]]);
###                         [ 1     2     3     4     5]
###                         [                          ]
###                         [ 2     3     4     5     6]
###                    A := [                          ]
###                         [ 4     1    -2    -5    -2]
###                         [                          ]
###                         [-1    -4    -2     1     2]
###
###
##> H := HermiteForm[Z](A);
##< Matrix( [1,0,-1,-1,-3],[0,1,2,3,4],[0,0,5,11,3],[0,0,0,0,6]]);
###                            [1    0    -1    -2    -3]
###                            [                        ]
###                            [0    1     2     3     4]
###                       H := [                        ]
###                            [0    0     5    11     3]
###                            [                        ]
###                            [0    0     0     0     6]
###
##> H, U := HermiteForm[Z](A,output=['H','U']);
###                 [1    0    -1    -2    -3]  [ -3     2     0    0]
###                 [                        ]  [                    ]
###                 [0    1     2     3     4]  [  2    -1     0    0]
###         H, U := [                        ], [                    ]
###                 [0    0     5    11     3]  [-15    12    -2    1]
###                 [                        ]  [                    ]
###                 [0    0     0     0     6]  [ 10    -7     1    0]
###
##> MatrixMatrixMultiply[Z](U,A); # Check that U A = H
##                           [1    0    -1    -2    -3] 
##                           [                        ]
##                           [0    1     2     3     4]
##                           [                        ]
##                           [0    0     5    11     3]
##                           [                        ]
##                           [0    0     0     0     6]   
##< H;
##
## Using positive range for the remainder, given by modp(a,b).
##> Z[Quo] := proc(a,b,r) local q,rr;
##>   rr := Z[Rem](a,b,'q');
##>   if nargs=3 then r := rr fi;
##>   q;
##> end:
##> Z[Rem] := proc(a,b,q) local r,qq;
##>   r := modp(a,b);
##>   if nargs=3 then q := iquo(a-r,b); fi;
##>   r;
##> end:
##> H := HermiteForm[Z](A);
##< Matrix([[1,0,4,9,0],[0,1,2,3,4],[0,0,5,11,3],[0,0,0,0,6]]);
###                          [1    0    4     9    0]
###                          [                      ]
###                          [0    1    2     3    4]
###                     H := [                      ]
###                          [0    0    5    11    3]
###                          [                      ]
###                          [0    0    0     0    6]
###
##> U := HermiteForm[Z](A,output='U');
###                           [-18    14    -2    1]
###                           [                    ]
###                           [  2    -1     0    0]
###                     U :=  [                    ]
###                           [-15    12    -2    1]
###                           [                    ]
###                           [ 10    -7     1    0]
###
##> MatrixMatrixMultiply[Z](U,A);
##< H;
###                          [1    0    4     9    0]
###                          [                      ]
###                          [0    1    2     3    4]
###                          [                      ]
###                          [0    0    5    11    3]
###                          [                      ]
###                          [0    0    0     0    6]
###
##

HermiteForm := proc(B::Matrix,out::{name,
    identical(output)={identical(U),identical(H),list({identical(U),identical(H)})}})

local E,m,n,i,A,u,n2,zero,one,rw,pivrow,pivcol,zeroOutIJPosWithPiv,cleanWithPiv,makePivUnitNormal;

  E := GenericCheck( procname, HermiteFormOperations );
  n2 := evalb(nargs=2);
  A := Matrix(B);
  n,m := op(1,A);

  zero := E[`0`];
  one := E[`1`];
  if n2 then
    u := Matrix(n,n,'fill'=zero);
    for i to n do u[i,i] := one; end do;
  end if;

  zeroOutIJPosWithPiv := proc()
  local g,s,t,a,b,j,temp:
    g := E[Gcdex](A[pivrow,pivcol], A[rw,pivcol], 's', 't');
    a := E[Quo](A[pivrow,pivcol],g);
    b := E[Quo](A[rw,pivcol],g);
    #
    #  We have  s A[pivrow,pivcol]/g + t A[rw,pivcol]/g = 1
    #
    #   [  s  t ]  [ A[pivrow,pivcol]  A[pivrow,j] ]    [ g  ... ]
    #   [       ]  [                               ] =  [        ]
    #   [ -b  a ]  [   A[rw,pivcol]      A[rw,j]   ]    [ 0  ... ]
    #
    #   for j = (pivcol+1)..m  where note  s a + t b = 1
    #
    #note, g is unit normal as Gcdex(...) mod p guarantees this so we have no need to make
    #the pivot in row pivrow unit normal.
    for j from pivcol+1 to m do
      temp := E[`+`]( E[`*`](s,A[pivrow,j]), E[`*`](t,A[rw,j]) );
      A[rw,j] := E[`-`]( E[`*`](a,A[rw,j]), E[`*`](b,A[pivrow,j]));
      A[pivrow,j] := temp;
    end do;
    A[pivrow,pivcol] := g;
    A[rw,pivcol] := zero;
    if n2 then
      for j to n do
        temp := E[`+`](E[`*`](s,u[pivrow,j]),E[`*`](t,u[rw,j]));
        u[rw,j] := E[`-`](E[`*`](a,u[rw,j]),E[`*`](b,u[pivrow,j]));
        u[pivrow,j] := temp;
      end do;
    end if;
  end proc:

  cleanWithPiv := proc()
  local i,q,t,j:
    for i to pivrow-1 do
      q := E[Quo](A[i,pivcol],A[pivrow,pivcol],'t');
      if E[`=`](q,zero) then next end if;
      for j from pivcol+1 to m do
        A[i,j] := E[`-`](A[i,j],E[`*`](q,A[pivrow,j]));
      end do;
      A[i,pivcol] := t;
      if n2 then
        for j to n do u[i,j] := E[`-`](u[i,j],E[`*`](q,u[pivrow,j]))
        end do;
      end if;
    end do;
  end proc:

  makePivUnitNormal := proc()
  local L,inv,j:
    L := E[UnitPart](A[pivrow,pivcol]);
    inv := E[Quo](one,L);
    if not E[`=`](L,E[`1`]) then
      for j from pivcol to m do A[pivrow,j] := E[`*`](inv,A[pivrow,j]) end do;
      if n2 then
        for j to n do u[pivrow,j] := E[`*`](inv,u[pivrow,j]) end do;
      end if;
    end if;
  end proc:

  for rw from 2 to n do
    pivrow,pivcol := 1,1:
    while pivrow <= rw and pivcol <= m do
      if pivrow < rw then
        if not E[`=`](A[rw,pivcol],zero) then
          #zero out A[rw,pivcol] using A[pivrow,pivcol]
          userinfo(2,procname,`elimination using pivot in position`,pivrow,pivcol);
          zeroOutIJPosWithPiv();
          #reduce the entries above A[pivrow,pivcol] so that their degrees are less than that of A[pivrow,pivcol].
          #It may be that A[pivrow,pivcol] = 0, in this case we can't reduce the entries above A[pivrow,pivcol].
          if not E[`=`](A[pivrow,pivcol],zero) then 
            cleanWithPiv();
          end if:
          pivrow := pivrow + 1:
        else
          #When entering the "else" clause, we also know that A[rw,pivcol]=0 now so we don't
          #have to zero out A[rw,pivcol], but we must still reduce the entries above A[pivrow,pivcol].
          #We also may need to make the pivot in row pivrow unit normal, so we begin with that
          if not E[`=`](A[pivrow,pivcol],zero) then
            makePivUnitNormal();
            cleanWithPiv();
            pivrow := pivrow + 1:
          end if:
        end if:
      else
        #if we enter this else statement we know that pivrow = rw. There is no zeroing out to do to put the
        #upper rw by cl submatrix of A into Hermite form, but we must reduce the entries above A[pivrow,pivcol]
        #so degrees are strictly less than the degree of A[pivrow,pivcol].
        if not E[`=`](A[pivrow,pivcol],zero) then
          #We also may need to make the pivot in row pivrow unit normal, so we begin with that.
          makePivUnitNormal();
          cleanWithPiv();
          pivrow := pivrow + 1:
        end if:
      end if:
      pivcol := pivcol + 1:
    end do:
  end do:
  if nargs=1 then return A fi;
  if type(out,name) then out := u; return A; fi;
  A := subs( {'H'=A,'U'=u}, rhs(out) );
  if type(rhs(out),list) then op(A) else A fi;
end proc:

## CALLINGSEQ
##- SmithForm[E](A)
##- SmithForm[E](A,output=out)
##
##PARAMETERS
##- E     : the domain of computation, an Euclidean domain
##- A     : m by n Matrix of values in E
##- out   : one of 'S', 'U', or 'V', or a list containing one or more of these names
##
##RETURNS
##
##- SmithForm[E](A) returns an m by n matrix S of values in E.
##
##- SmithForm[E](A,output=['S','U','V']) returns the matrix S
##  and also multipier matrices U, an m by m matrix of values in E,
##  and V an n by n matrix of values in E, satisfying U A V = S .
##
##SYNOPSIS
##- SmithForm[E](A) returns the Smith Normal Form S of A which satisfies
##    (1) S[i,j] = 0 if i<>j
##    (2) S[i,i] is unit normal in E (implies uniqueness)
##    (3) S[i,i] | S[i+1,i+1] for all 1<=i<min(m,n) 
##    (4) prod(S[i,i],i=1..d) = u*gcd(all minors of A of dimension d) where u is a unit
##    (5) S[i,i] = 0 for r < i <= min(m,n) where r is the rank of A
##
##- The (indexed) parameter E, which specifies the domain of computation, a Euclidean domain,
##  must be a Maple table (or module) which has the following values (exports):
##
##  E[`0`]: a constant for the zero of the ring E
##  E[`1`]: a constant for the (multiplicative) identity of E
##  E[`+`]: a procedure for adding elements of E (nary)
##  E[`-`]: a procedure for negating and subtracting elements of E (unary and binary)
##  E[`*`]: a procedure for multiplying two elements of E (commutative)
##  E[`=`]: a boolean procedure for testing if two elements in F are equal
##  E[Quo]: a procedure which computes the quotient of a divided by b.
##          E[Quo](a,b,'r') computes the quotient q of a divided b and
##          optionally assigns r the remainder satisfying a = b q + r.
##  E[Rem]: a procedure for finding the remainder of a divided by b.
##          E[Rem(a,b,'q') computes the remainder r of a divided b and
##          optionally assigns q the quotient satisfying a = b q + r.
##  E[Gcdex]: a procedure for finding the gcd g of a anb b, an element of E.
##          E[Gcdex](a,b,'s','t') computes the gcd of a and b and
##          optionally assigns s and t elements of E satisfying s a + t b = g.
##  E[UnitPart]: a procedure for returning the unit part of an element in E
##  E[EuclideanNorm]: a procedure for computing the Euclidean norm of an 
##          element in E, a non-negative integer.
##
## For non-zero a,b in E, units u,v in E, the Euclidean norm N satisfies
##          N(a b) >= N(a)
##          N(u) = N(v) and N(u a) = N(a)
##
##- The Smith form is computed by first computing H the Hermite form of
##  A then computing the Hermite form of H transpose.  If the resulting
##  matrix is not diagonal, often it is, then the above sequence of
##  computations is repeated, usually once, until it is.
##
##EXAMPLE
##
##> with(GenericLinearAlgebra):
##> (Z[`0`],Z[`1`],Z[`+`],Z[`-`],Z[`*`],Z[`=`]) := (0,1,`+`,`-`,`*`,`=`):
##> Z[Gcdex] := igcdex:
##> Z[Quo] := iquo:
##> Z[Rem] := irem:
##> Z[UnitPart] := sign:
##> Z[EuclideanNorm] := abs:
##> A := Matrix([[1,2,3,4,5],[2,3,4,5,6],[4,1,-2,-5,-2],[-1,-4,-2,1,2]]);
###                         [ 1     2     3     4     5]
###                         [                          ]
###                         [ 2     3     4     5     6]
###                    A := [                          ]
###                         [ 4     1    -2    -5    -2]
###                         [                          ]
###                         [-1    -4    -2     1     2]
###
###
##> S := SmithForm[Z](A);
##< Matrix([1,0,0,0,0],[0,1,0,0,0],[0,0,1,0,0],[0,0,0,6,0]]);
###                           [1    0    0    0    0]
###                           [                     ]
###                           [0    1    0    0    0]
###                      S := [                     ]
###                           [0    0    1    0    0]
###                           [                     ]
###                           [0    0    0    6    0]
###
###
##> U,V := SmithForm[Z](A,output=['U','V']);
###                                      [1    0     0     3     1]
###              [ -3     2     0    0]  [                        ]
###              [                    ]  [0    1     1    -7    -7]
###              [  2    -1     0    0]  [                        ]
###              [                    ], [0    0    -2     6    11]
###              [-15    12    -2    1]  [                        ]
###              [                    ]  [0    0     1    -3    -5]
###              [ 10    -7     1    0]  [                        ]
###                                      [0    0     0     1     0]
###
##> MatrixMatrixMultiply[Z](MatrixMatrixMultiply[Z](U,A),V);
##< S;
###                          [1    0    0    0    0]
###                          [                     ]
###                          [0    1    0    0    0]
###                          [                     ]
###                          [0    0    1    0    0]
###                          [                     ]
###                          [0    0    0    6    0]
###

SmithForm := proc(A::Matrix,
   out::identical(output)={identical(S),identical(U),identical(V),
                           list({identical(S),identical(U),identical(V)})} )
local E,B,m,n,u,v,i,j,n2,zero,one,r,g,a,b,k,temp,t,s,Checkdiag,U1,V2;

  E := GenericCheck( procname, SmithFormOperations );
  n2 := evalb(nargs>=2);
  B := Matrix(A);
  m,n := LinearAlgebra:-Dimensions(B);
  zero := E[`0`];
  one := E[`1`];
  if n2 then
    u := Matrix(m,m,'fill'=zero);
    v := Matrix(n,n,'fill'=zero);
    for i to m do u[i,i]:=one od;
    for i to n do v[i,i]:=one od;
  fi;

  # Assume B is in Hermite Normal Form
  # check if B is in diagonal form
  # i.e. check if entries above diagonal are zero
  Checkdiag := proc()
  local m,n,i,j;
    m,n := LinearAlgebra:-Dimensions(B);
    for j from 2 to min(m,n) do
      if not E[`=`](B[j,j],zero) and E['EuclideanNorm'](B[j,j]) = 0 then next fi;
      for i to j-1 do
        if not E[`=`](B[i,j],zero) then return false fi;
      od;
    od;
    for j from m+1 to n do
      for i to m do
        if not E[`=`](B[i,j],zero) then return false fi;
      od;
    od;
    return true;
  end:
    
  while true do
    if n2 then
      B := HermiteForm[E](B,'U1');
      u := MatrixMatrixMultiply[E](U1,u);
    else
      B := HermiteForm[E](B);
    fi;
    if Checkdiag() then break fi;
    B := LinearAlgebra:-Transpose(B);

    if n2 then
      B := HermiteForm[E](B,'V2');
      v := MatrixMatrixMultiply[E](V2,v);
    else
      B := HermiteForm[E](B);
    fi;
    if Checkdiag() then
      B := LinearAlgebra:-Transpose(B);
      break;
    fi;
    B := LinearAlgebra:-Transpose(B);
  od;
  if n2 then
    v := LinearAlgebra:-Transpose(v);
  fi;

  r := min(m,n);
  for i to min(m,n) do
    if E[`=`](B[i,i],zero) then
      r:=i-1;
      break;
    fi;
  od;
  #  At this point, B is diagonal: B[i,i] is zero for i>r
  #  Now make B[i,i] | B[i+1,i+1] for 1 <= i < r
  for i to r-1 do
    for j from i+1 to r while B[i,i] <> one do
      g := E['Gcdex'](B[i,i],B[j,j],'s','t');
      a := E['Quo'](B[i,i],g);
      B[i,i] := g;
      if n2 then
        b := E['Quo'](B[j,j],g);
	for k to m do
	  temp := E[`+`](E[`*`](s,u[i,k]),
                         E[`*`](t,u[j,k]));
          u[j,k] := E[`-`](E[`*`](a,u[j,k]),
                           E[`*`](b,u[i,k]));
	  u[i,k] := temp;
        od;
        t := E[`*`](t,b);
        s := E[`-`](one,t);
        for k to n do
          temp := E[`+`](v[k,i],v[k,j]);
          v[k,j] := E[`-`](E[`*`](s,v[k,j]),
			    E[`*`](t,v[k,i]));
          v[k,i] := temp;
        od;
      fi;
      B[j,j] := E[`*`](a,B[j,j])
    od
  od;

  if nargs=1 then return B; fi;
  B := subs( {'S'=B,'U'=u,'V'=v}, rhs(out) );
  if type(rhs(out),list) then op(B) else B fi;
end:


end:

#savelib('GenericLinearAlgebra');
