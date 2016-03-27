/**
 * http://www.lexicalscope.com/blog/2015/04/10/dafny-sum-and-max-solution/
 */

method SumMax(a: array<int>) returns (sum: int, max: int)
	requires a != null;
	requires a.Length >= 0;
	requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;
	ensures sum <= a.Length*max;
	ensures forall i :: 0 <= i < a.Length ==> a[i] <= max;
	ensures a.Length > 0 ==> exists i :: 0 <= i < a.Length && a[i] == max;
	ensures sum == Sum(a);
{
	max := 0;
	sum := 0;

	var idx := 0;
	while idx < a.Length 
		invariant idx <= a.Length
		invariant forall i :: 0 <= i < idx ==> a[i] <= max
		invariant max > 0 ==> exists i :: 0 <= i < idx && a[i] == max
		invariant sum <= idx * max
		invariant sum == Sum'(a, 0, idx);
	{
		if (max < a[idx])
		{
			max := a[idx];
		}
		sum := sum + a[idx];
		idx := idx + 1;
	}
}
	
function Sum(a: array<int>) : int
	reads a;
	requires a != null;
{
	Sum'(a, 0, a.Length)
}
	
function Sum'(a: array<int>, i: int, j: int) : int
	requires a != null
	requires 0 <= i <= j <= a.Length
	reads a
{
	if j == i then 0 else Sum'(a, i, j-1) + a[j-1]
}
	
lemma SumOfIntervalOneIsElement(a: array<int>, i: int)
	requires a != null;
	requires 0 <= i < a.Length;
	ensures a.Length > 0;
	ensures Sum'(a, i, i+1) == a[i];
{ }
	
lemma SumOfIntervalIsSumOfSubIntervals
		(a: array<int>, i: int, j: int, k: int)
	requires a != null;
	requires 0 <= i <= j <= k <= a.Length;
	ensures Sum'(a, i, j) + Sum'(a, j, k) == Sum'(a, i, k);
{ }