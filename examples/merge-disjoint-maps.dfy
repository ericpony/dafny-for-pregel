method MergeMaps<V> (a: map<int,V>, b: map<int,V>, n: int) returns (m: map<int,V>)
	requires a !! b
	requires n > 0
	requires forall i :: i in a ==> 0 <= i < n
	requires forall i :: i in b ==> 0 <= i < n
	ensures forall i :: i in m ==> 0 <= i < n
	ensures forall i :: i in m && i in a ==> m[i] == a[i]
	ensures forall i :: i in m && i in b ==> m[i] == b[i]
	ensures forall i :: i in m ==> i in a || i in b
{
	m := a;
	var i := 0;
	assert forall j :: j in a <==> j in m;
	while i < n
		invariant 0 <= i <= n
		invariant forall i :: i in a ==> i in m
		invariant forall i :: i in a ==> m[i] == a[i]
		invariant forall i :: i in m ==> 0 <= i < n
		invariant forall i :: i in m ==> i in a || i in b
		invariant forall j :: 0 <= j < i ==> j in b ==> j in m
		invariant forall j :: 0 <= j < i ==> j in b ==> m[j] == b[j]
	{
		if i in b {
			m := m[i := b[i]];
			assert m[i] == b[i];
		}
		i := i + 1;
	}
}
