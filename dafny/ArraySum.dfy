method ArraySum (a : array<int>, b : array<int>) returns (c : array<int>)
    requires a.Length == b.Length
    ensures c.Length == a.Length
    ensures forall i : int :: 0 <= i < a.Length ==> a[i] + b[i] == c[i]
{
    c := new int [a.Length];
    var i : int := 0;
    while (i < a.Length)
        invariant i <= a.Length
        invariant forall j : int :: 0 <= j < i ==> c[j] == a[j] + b[j]
    {
        c[i] := a[i] + b[i];
        i := i + 1;
    }
}