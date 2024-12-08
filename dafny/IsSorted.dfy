method IsSorted (a : array<int>) returns (isSorted : bool)
    requires a.Length > 0 // Does not work when length is 0 for some reason
    ensures isSorted <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] <= a[j]
{
    isSorted := true;
    var i : int := 1;
    if (a.Length < 2)
    {
         
    }
    else
    {
        while (i < a.Length)
            invariant i <= a.Length && (isSorted <==> forall j : int :: 1 <= j < i ==> a[j - 1] <= a[j])
        {
            if a[i-1] > a[i]
            {
                isSorted := false;
                i := a.Length;
            } else {
                i := i+1;
            }
        }
    }
}