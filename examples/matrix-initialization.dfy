method InitializeMatrix(mat: array2<bool>, n: nat)
	requires mat != null && mat.Length0 == n && mat.Length1 == n
	modifies mat
	ensures forall i,j | 0 <= i < n && 0 <= j < n :: !mat[i,j]
{
	var src := 0;
	assert  forall i,j | 0 <= i < src && 0 <= j < n :: !mat[i,j];
	while src < n
		invariant src <= n
		invariant forall i,j | 0 <= i < src && 0 <= j < n :: !mat[i,j]
	{
		var dst := 0;
		while dst < n
			invariant dst <= n
			invariant forall j | 0 <= j < dst :: !mat[src,j]
			invariant forall i,j | 0 <= i < src && 0 <= j < n :: !mat[i,j]
		{
			mat[src,dst] := false;
			dst := dst + 1;
		}
		assert forall j | 0 <= j < n :: !mat[src,j];
		src := src + 1;
	}
	assert forall i,j | 0 <= i < n && 0 <= j < n :: !mat[i,j];
}