/**
 * Demonstrate a bug of Dafny and its workaround.
 * See https://dafny.codeplex.com/workitem/144 for details.
 */

class ExistentiallyQuantifiedPredicateBug
{
	var arr : array<int>;

	predicate p(i: int)

	method foo()
		requires arr != null && arr.Length > 0
		modifies arr
	{
		assume exists i :: p(i);
		ghost var i :| p(i);
		arr[0] := 1;
		assert p(i);
		assert exists i :: p(i); // FAILS without assert p(i)
	}

	predicate q(i: int, j: int)

	predicate q'(i: int)
		requires arr != null && arr.Length > 0
		reads this`arr
	{
		exists j | 0 <= j < arr.Length :: q(i, j)
	}

	method goo()
		requires arr != null && arr.Length > 0
		modifies arr
	{
		assume forall i | 0 <= i < arr.Length :: q'(i);
		var i := 0;
		while i < arr.Length {
			assert q'(i);
			arr[i] := i;
			i := i + 1;
		}
	}

}

predicate p(i:int)

method m3()

method m1()
{}

method m2()
{
  assume exists i :: p(i);
  ghost var i :| p(i);
  m1();
  assert p(i);
  assert exists i :: p(i); // FAILS without assert p(i)
}