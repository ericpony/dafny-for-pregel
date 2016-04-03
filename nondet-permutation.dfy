/**
 * Given N >= 0, generate a permuation of {0,...,N-1} nondeterministically.
 */
method Permutation(N: int) returns (perm: array<int>)
	requires N >= 0
	ensures perm != null
	ensures perm.Length == N
	ensures distinct(perm)
	ensures forall i :: 0 <= i < perm.Length ==> 0 <= perm[i] < N
{
	var all := set x | 0 <= x < N;
	var record := {};
	perm := new int[N];
	CardinalityLemma(N, all);
	while record < all
		invariant record <= all
		invariant |record| <= |all|
		invariant forall i :: 0 <= i < |record| ==> perm[i] in record
		invariant distinct'(perm, |record|)
		decreases |all| - |record|
	{
		CardinalityOrderingLemma(record, all);
		var dst :| dst in all && dst !in record;
		perm[|record|] := dst;
		record := record + {dst};
	}
	assert record == all;
	print perm;
}

predicate distinct(a: array<int>)
	requires a != null
	reads a
{
	distinct'(a, a.Length)
}

predicate distinct'(a: array<int>, n: int)
	requires a != null
	requires a.Length >= n 
	reads a
{
	forall i,j :: 0 <= i < n && 0 <= j < n && i != j ==> a[i] != a[j]
}

lemma CardinalityLemma (size: int, s: set<int>) 
	requires size >= 0
	requires s == set x | 0 <= x < size
	ensures	size == |s|
{
	if(size == 0) {
		assert size == |(set x | 0 <= x < size)|;
	} else {
		CardinalityLemma(size - 1, s - {size - 1});
	}
}

lemma CardinalityOrderingLemma<T> (s1: set<T>, s2: set<T>)
	requires s1 < s2
	ensures |s1| < |s2|
{
	var e :| e in s2 - s1;
	if (s1 == s2 - {e}) {
		assert |s1| == |s2| - 1;
	} else {
		CardinalityOrderingLemma(s1, s2 - {e});
	}
}