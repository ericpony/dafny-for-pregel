/**
 * This example shows that Dafny has problems with quantidfied annotations.
 * See https://dafny.codeplex.com/workitem/146 for discussions.
 */

function method inhabited(world: array2<bool>): bool
	requires world != null
{
	exists i,j :: 0 <= i < world.Length0 && 0 <= j < world.Length1 && world[i,j]
}

method GameOfLife(size: nat, N: nat)
{
	var world := new bool[size,size];
	var n := 0;
	while inhabited(world) && n < N
	{
		forall i,j | 0 <= i < size && 0 <= j < size
		{
			world[i,j] := false;
		}
		assert inhabited(world);
		// ...
		n := n + 1;
	}
}