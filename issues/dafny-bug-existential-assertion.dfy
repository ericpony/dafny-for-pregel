/**
 * This example shows that Dafny may accept incorrect assertions.
 * See https://dafny.codeplex.com/workitem/145 for discussions.
 */

predicate existential(mat: array2<bool>)
	requires mat != null
{
	exists i,j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 && mat[i,j]
}

predicate universal(mat: array2<bool>)
	requires mat != null
{
	forall i,j :: 0 <= i < mat.Length0 && 0 <= j < mat.Length1 ==> !mat[i,j]
}

method foo(n: nat)
{
	var mat := new bool[n,n];
	forall i,j | (0 <= i < n && 0 <= j < n)
	{
		mat[i,j] := false;
	}
	var i := 0;
	while i < n
	{
		var j := 0;
		while j < n
		{
			mat[i,j] := true;
			j := j + 1;
		}
		i := i + 1;
	}
	//assert !existential(mat); // wrongly verified by Dafny
	//assert universal(mat);    // wrongly verified by Dafny
}