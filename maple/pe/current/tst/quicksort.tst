#test

######################################################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "../lib":

######################################################################

swap := proc(A, x, y) 
    local temp;
    temp := A[x];
    A[x] := A[y];
    A[y] := temp;
end proc:

partition := proc(A, m, n, pivot, compare)
    local pivotIndex, pivotValue, storeIndex, i, temp;
    pivotIndex := pivot(A, m, n);
    pivotValue := A[pivotIndex];
    swap(A, pivotIndex, n);
    storeIndex := m;
    for i from m to n-1 do
        if compare(A[i], pivotValue) then
            swap(A, storeIndex, i);
            storeIndex := storeIndex + 1;
        end if;
    end do;
    swap(A, n, storeIndex);
    return storeIndex;
end proc:

quicksort := proc(A, m, n, pivot, compare)
    local p;
    if m < n then
        p := partition(A, m, n, pivot, compare);
        quicksort(A, m, p-1, pivot, compare);
        quicksort(A, p+1, n, pivot, compare);
    end if;
end proc:

######################################################################


qs1 := proc(A, m, n) local p, c;
    p := (A, m, n) -> n;
    c := `<=`;
    quicksort(A, m, n, p, c)
end proc:

qs2 := proc(A, m, n)
    quicksort(A, m, n, (A, m, n) -> n, `>`)
end proc:

qs3 := proc(A, m, n)
    quicksort(A, m, n, (A, m, n) -> rand(m..n)(), `<=`);
end proc:

######################################################################

# TODO, need to unfold the call into ModuleApply

mm := module()
    quicksort_1 := proc(A, m, n)
        local p;
        if m < n then
            p := partition_1(A, m, n);
            quicksort_1(A, m, p - 1);
            quicksort_1(A, p + 1, n)
        end if
    end proc;

    partition_1 := proc(A, m, n)
        local pivotIndex, pivotValue, temp1, storeIndex, i, temp2, temp3;
        pivotIndex := n;
        pivotValue := A[pivotIndex];
        temp1 := A[pivotIndex];
        A[pivotIndex] := A[n];
        A[n] := temp1;
        storeIndex := m;
        for i from m to n - 1 do
            if A[i] <= pivotValue then
                temp2 := A[storeIndex];
                A[storeIndex] := A[i];
                A[i] := temp2;
                storeIndex := storeIndex + 1
            end if
        end do;
        temp3 := A[n];
        A[n] := A[storeIndex];
        A[storeIndex] := temp3;
        return storeIndex
    end proc

end module;

opts := PEOptions():
opts:-setConsiderExpseq(false):

pe_qs1 := OnPE(qs1, opts):

got1 := op(5, ToInert(eval(pe_qs1:-quicksort_1)));
got2 := op(5, ToInert(eval(pe_qs1:-partition_1)));

expected1 := op(5, ToInert(eval(mm:-quicksort_1)));
expected2 := op(5, ToInert(eval(mm:-partition_1)));

Try(101, got1, expected1);
Try(102, got2, expected2);

#######################################################################

#end test
