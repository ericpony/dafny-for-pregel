predicate isArray<T> (arr: array<T>, size: nat)
{
	arr != null && arr.Length == size
}

predicate isIdentityMatrix (mat: array<array<int>>, size: nat)
	requires isArray(mat, size)
	reads mat, mat[..]
{
	forall i,j | 0 <= i < size && 0 <= j < size ::
		isArray(mat[i], size) && mat[i][j] == if i == j then 1 else 0
}