
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


M:-Print(M:-ToM(ToInert(eval(partition))));

opts := PEOptions():
opts:-setConsiderExpseq(false):
pe_qs1 := OnPE(qs1, opts):

printmod(pe_qs1);

a := Array([4,5,1,8,2,0,3,7,6,9]);
qs1(a,1,10);
print(a);


a := Array([4,5,1,8,2,0,3,7,6,9]);
pe_qs1(a, 1, 10);
print(a);
