/**
	* Source:
	* http://dafny.codeplex.com/workitem/157
	*/

function add(e1:int, e2:int) : int {
	e1 + e2
}

function exp(x:int, e:int):int
	requires e >= 0 
{ 
	if e == 0 then 1 else x * exp(x, e - 1) 
}

lemma L1 (b:int, e1:int, e2:int)
	requires e1 >= 0 && e2 >= 0
	// POINT: Dafny will timeout if we use e1 + e2 instead of add(e1, e2)
	// ensures exp(b, e1 + e2) == exp(b, e1) * exp(b, e2)
	ensures exp(b, add(e1, e2)) == exp(b, e1) * exp(b, e2) 
{
	if e1 > 0 {
		L1(b, e1 - 1, e2);
	}
}

/* Use calc */
lemma L2 (b:int, e1:int, e2:int)
	requires e1 >= 0 && e2 >= 0
	// POINT: Dafny will timeout if we use e1 + e2 instead of add(e1, e2)
	// ensures exp(b, e1 + e2) == exp(b, e1) * exp(b, e2)
	ensures exp(b, add(e1, e2)) == exp(b, e1) * exp(b, e2)
{
	if e1 > 0 {
		calc {
			exp(b, e1 + e2);
			== { L2(b, e1 - 1, e2); }
			exp(b, e1) * exp(b, e2);
		}
	}
}