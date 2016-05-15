predicate TotalPreorder<T> (R : (T, T) -> bool)
  reads R.reads
{
     (forall x, y :: R.requires(x, y))
  && (forall x, y :: R(x, y) || R(y, x))
  && (forall x, y, z :: R(x, y) && R(y, z) ==> R(x, z))
}

method Main()
{
  var a : int, b : int, c : int;
		
  ghost var Leq: (int, int) -> bool;
  assume TotalPreorder(Leq);

  assume Leq(a, b);
  assume Leq(b, c);

  // Transitivity
  assert Leq(a, c);

  // Reflexivity
  assert Leq(a, a);

  // Totalness
  assert forall x, y :: Leq(x, y) || Leq(y, x);
}