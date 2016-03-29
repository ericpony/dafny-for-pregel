/**
 * This example shows that Dafny may accept incorrect assertions.
 *
 * (Confirmed at http://rise4fun.com/Dafny, 2016-03-29,
 * and by the stable version 1.9.6 released on Oct 12, 2015.
 * Seems to be fixed in change sets after Jan 2016.)
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