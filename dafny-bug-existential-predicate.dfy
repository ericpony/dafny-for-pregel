/**
 * Demonstrate a bug of Dafny described in https://dafny.codeplex.com/workitem/144
 */

class ExistentiallyQuantifiedPredicateBug
{
	var arr : array<int>;
	predicate p(i:int)
	method foo()
		requires arr != null && arr.Length > 0
		modifies arr
	{
		assume exists i :: p(i);
		arr[0] := 1;
		assert exists i :: p(i); // FAILS
	}
}

predicate p(i:int)

method m3()

method m1()
	// a workaround
	requires exists i :: p(i)
	ensures exists i :: p(i) 
{}

method m2()
{
  assume exists i :: p(i);
  assert exists i :: p(i);
  m1();
  assert exists i :: p(i); // FAILS without workaround
}