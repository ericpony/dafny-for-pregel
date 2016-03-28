/**
 *  Challenge:
 *  Substitute a loop with valid invariants for the forall loop inside the main loop.
 */
method foo(n: int)
{
	var mat := new bool[n,n];
	forall i,j | (0 <= i < n && 0 <= j < n)
	{
		mat[i,j] := false;
	}
	var i := 0;
	var j := 0;
	while i < n
		invariant 0 <= i <= n && 0 <= j <= n
		invariant forall k, j :: 0 <= k < i && 0 <= j < n ==> mat[k,j];
	{
		forall j: int | 0 <= j < n { mat[i,j] := true; }
		/*
		Cannot verify the following loop:
		while j < n
			invariant 0 <= i <= n && 0 <= j <= n
			invariant forall i, j :: 0 <= i < i && 0 <= j < j ==> mat[i,j];
		{
			mat[i,j] := true;
			j := j + 1;
		}
		*/
		i := i + 1;
	}
	assert forall i, j :: 0 <= i < n && 0 <= j < n ==> mat[i,j];
}