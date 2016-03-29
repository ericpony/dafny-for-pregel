method foo(n: nat)
{
	var mat := new bool[n,n];
	forall i,j | 0 <= i < n && 0 <= j < n
	{
		mat[i,j] := false;
	}
	var i := 0;
	var j := 0;
	while i < n
		invariant 0 <= i <= n
		invariant forall k :: 0 <= k < i ==> INV(mat, k)
		// The following invariant is syntactically equivalent 
		// to the above one but cannot be verified.
		// invariant forall k,j :: 0 <= k < i ==> 0 <= j < n ==> mat[k,j];
	{
		// In the latest version of Dafny (after Jan 2016), a forall loop 
		// no longer implies its equivalent forall assertion trivially:
		//		forall j | 0 <= j < n { mat[i,j] := true; }
		//		assert forall j :: 0 <= j < n ==> mat[i,j]; //FAILED!
		j := 0;
		while j < n
			invariant j <= n;
			invariant forall k :: 0 <= k < j ==> mat[i,k];
		{
			mat[i,j] := true;
			j := j + 1;
		}
		i := i + 1;
	}
}
predicate INV(mat: array2<bool>, i: int)
	requires mat != null
	requires 0 <= i < mat.Length0
{
	forall j :: 0 <= j < mat.Length1 ==> mat[i,j]
}