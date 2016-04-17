/**
 * Source:	
 * http://www.lexicalscope.com/blog/2014/11/11/dafny-triggers/
 */

predicate P(x: int) { true } 
 
lemma ThereIsMoreThanOneInteger(x: int)
	ensures exists z: int :: z != x
{ 
	assert P(x+1); // can't prove
}
 
lemma NoReallyThereIsMoreThanOneInteger(x: int)
	ensures exists z: int {:trigger P(z)} :: z != x
{ 
	assert P(x+1); // can prove
}