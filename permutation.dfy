/**
 * Source: http://www.lexicalscope.com/blog/2014/11/11/dafny-permutations-sequences-and-multisets/
 */

predicate Subpermutation(xs:seq,  ys:seq)
   ensures Subpermutation(xs, ys) ==> forall x :: x in xs ==> x in ys;
{
  assert forall x :: x in xs ==> x in multiset(xs);
  multiset(xs) <= multiset(ys)
}
 
// THEOREM
lemma SubpermutationIsSmaller(xs:seq,  ys:seq)
  requires Subpermutation(xs, ys);
  ensures |xs| <= |ys|;
{
  assert |multiset(xs)| == |xs|;
  assert |multiset(ys)| == |ys|;
 
  var xs', ys' := xs, ys; 
  var XS', YS' := multiset(xs), multiset(ys);
  var XS'', YS'' := multiset{}, multiset{};
  while(|XS'| > 0)
     invariant Subpermutation(xs', ys');
     invariant XS' == multiset(xs');
     invariant YS' == multiset(ys');
     invariant XS' + XS'' == multiset(xs);
     invariant YS' + YS'' == multiset(ys);
     invariant XS'' == YS'';
     invariant XS' <= YS';
  {
    var x := xs'[0];
    xs' := Remove(x, xs'); 
    ys' := Remove(x, ys'); 
    XS' := XS'[x := XS'[x] - 1];
    XS'' := XS''[x := XS''[x] + 1];
    YS' := YS'[x := YS'[x] - 1];
    YS'' := YS''[x := YS''[x] + 1];    
  }
}
 
// SUPPORTING DEFINITIONS

predicate RemoveFromSequenceReducesMultiSet<T> (xs:seq<T>,  XS':multiset<T>)
   requires xs != [];
   requires XS' == multiset(xs[1..]);
   ensures XS' == multiset(xs)[xs[0] := multiset(xs)[xs[0]] - 1];
{
  assert [xs[0]] + xs[1..] == xs;
  assert multiset([xs[0]] + xs[1..]) == multiset(xs);  
  true
}
 
function Remove<T> (x:T, xs:seq<T>): seq<T>
   requires x in xs;
   ensures multiset(Remove(x, xs)) == multiset(xs)[x := multiset(xs)[x] - 1];
   ensures |Remove(x, xs)| + 1 == |xs|;
{
     //assert multiset(xs[1..]) == multiset(xs)[xs[0] := multiset(xs)[xs[0]] - 1];
     assert RemoveFromSequenceReducesMultiSet(xs, multiset(xs[1..]));
     if xs[0] == x 
     then xs[1..] 
     else [xs[0]] + Remove(x, xs[1..])
}