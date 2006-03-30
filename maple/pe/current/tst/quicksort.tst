#test

######################################################################

with(TestTools):
kernelopts(opaquemodules=false):

libname := libname, "../lib":

######################################################################
# In-place quicksort on arrays


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

# pivot is last element
qs1 := proc(A, m, n) local p, c;
    p := (A, m, n) -> n;
    c := `<=`;
    quicksort(A, m, n, p, c)
end proc:


qs2 := proc(A, m, n) local middle, p, c;

    middle := proc(mid, y, z)
        (mid >= y and mid <= z) or (mid >= z and mid <= y)
    end proc;

    p := proc(A, m, n) local midindex, x, y, z;
        midindex := iquo(m+n,2);
        x := A[m];
        y := A[n];
        z := A[midindex];
        if middle(x, y, z) then
            m
        elif middle(y, x, z) then
            n
        elif middle(z, x, y) then
            midindex;
        end if;
    end proc;

    c := `>`;
    quicksort(A, m, n, p, c)
end proc:

qs3 := proc(A)
    quicksort(A, 10, 9);
end proc;

######################################################################

# TODO, need to unfold the call into ModuleApply

mm := module()
    quicksort_1 := proc(A, m, n)
        local midindex1, x1, y4, z4, m5, pivotIndex1, pivotValue1, temp1, storeIndex1, i1, temp2, temp3, p;
        if m < n then
            midindex1 := iquo(m + n, 2);
            x1 := A[m];
            y4 := A[n];
            z4 := A[midindex1];
            if y4 <= x1 and x1 <= z4 or z4 <= x1 and x1 <= y4 then m5 := m
            else
                if x1 <= y4 and y4 <= z4 or z4 <= y4 and y4 <= x1 then m5 := n
                else
                    if x1 <= z4 and z4 <= y4 or y4 <= z4 and z4 <= x1 then
                        m5 := midindex1
                    else m5 := NULL
                    end if
                end if
            end if;
            pivotIndex1 := m5;
            pivotValue1 := A[pivotIndex1];
            temp1 := A[pivotIndex1];
            A[pivotIndex1] := A[n];
            A[n] := temp1;
            storeIndex1 := m;
            for i1 from m to n - 1 do
                if pivotValue1 < A[i1] then
                    temp2 := A[storeIndex1];
                    A[storeIndex1] := A[i1];
                    A[i1] := temp2;
                    storeIndex1 := storeIndex1 + 1
                end if
            end do;
            temp3 := A[n];
            A[n] := A[storeIndex1];
            A[storeIndex1] := temp3;
            p := storeIndex1;
            quicksort_1(A, m, p - 1);
            quicksort_1(A, p + 1, n)
        end if
    end proc

end module;

opts := PEOptions():
opts:-setConsiderExpseq(false):

pe_qs2 := OnPE(qs2, opts):


got1 := op(5, ToInert(eval(pe_qs2:-quicksort_1)));

expected1 := op(5, ToInert(eval(mm:-quicksort_1)));

Try(201, got1, expected1);

######################################################################

# TODO, need to unfold the call into ModuleApply

mm := module()
    quicksort_1 := proc(A, m, n)
        local pivotIndex1, pivotValue1, temp1, storeIndex1, i1, temp2, temp3, p;
        if m < n then
            pivotIndex1 := n;
            pivotValue1 := A[pivotIndex1];
            temp1 := A[pivotIndex1];
            A[pivotIndex1] := A[n];
            A[n] := temp1;
            storeIndex1 := m;
            for i1 from m to n - 1 do
                if A[i1] <= pivotValue1 then
                    temp2 := A[storeIndex1];
                    A[storeIndex1] := A[i1];
                    A[i1] := temp2;
                    storeIndex1 := storeIndex1 + 1
                end if
            end do;
            temp3 := A[n];
            A[n] := A[storeIndex1];
            A[storeIndex1] := temp3;
            p := storeIndex1;
            quicksort_1(A, m, p - 1);
            quicksort_1(A, p + 1, n)
        end if
    end proc
end module;

opts := PEOptions():
opts:-setConsiderExpseq(false):

pe_qs1 := OnPE(qs1, opts):

got1 := op(5, ToInert(eval(pe_qs1:-quicksort_1)));

expected1 := op(5, ToInert(eval(mm:-quicksort_1)));

Try(101, got1, expected1);


######################################################################



#######################################################################


opts := PEOptions():
opts:-setConsiderExpseq(false):

pe_qs3 := OnPE(qs3, opts):

got := ToInert(eval(pe_qs3:-ModuleApply));
expected := ToInert(proc(A) end proc);

Try(300, got, expected);


#######################################################################


#end test
