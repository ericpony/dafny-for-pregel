/**
  * A cleanned-up version of the Pregel graph coloring algorithm.
  * Note that the proof in this version cannot be validated before
  * issue https://dafny.codeplex.com/workitem/146 is fixed.
  */

type VertexId = int
type Message = bool
type Color = int
type Weight = real

class PregelGraphColoring
{
	var numVertices: int;
	var vAttr : array<VertexId>;
	var vMsg : array<Message>;
	var msg : array2<Message>;
	var graph: array2<Weight>;
	var sent : array2<bool>;

	/**************************************
	 * Beginning of user-supplied functions
	 **************************************/

	method SendMessage(src: VertexId, dst: VertexId, w: Weight)
		requires valid1(vAttr) && valid2(sent) && valid2(msg)
		requires valid0(src) && valid0(dst)
		modifies msg, sent
		ensures sent[src, dst] ==> vAttr[src] == vAttr[dst];
		ensures !sent[src, dst] ==> vAttr[src] != vAttr[dst];
	{
		if vAttr[src] == vAttr[dst] {
			sent[src,dst] := true;
			sent[dst,src] := true;
			msg[src,dst] := true;
			msg[dst,src] := true;
		} else {
			sent[src,dst] := false;
			sent[dst,src] := false;
		}
	}

	function method MergeMessage(a: Message, b: Message): bool { a || b }

	method VertexProgram(vid: VertexId, msg: Message)
		requires valid0(vid) && valid1(vAttr)
		modifies vAttr
	{
		if msg == true {
			// choose a different color nondeterministically
			var newColor :| newColor >= 0 && newColor < vAttr.Length;
			vAttr[vid] := newColor;
		}
	}

	/***********************
	 * Correctness assertion
	 ***********************/


	function method correctlyColored(): bool
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		// adjacent vertices have different colors
		forall i,j :: 0 <= i < numVertices && 0 <= j < numVertices ==> 
			adjacent(i, j) ==> vAttr[i] != vAttr[j]
	}
	
	method Validated(maxNumIterations: nat) returns (res: bool)
		requires numVertices > 1 && maxNumIterations > 0
		requires valid1(vAttr) && valid2(graph) && valid2(sent) && valid2(msg)
		modifies this`numVertices, vAttr, msg, sent
		ensures res
	{
		var numIterations := pregel(maxNumIterations);
		res := numIterations <= maxNumIterations ==> correctlyColored();
	}

	function method noCollisions(): bool
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall vid :: 0 <= vid < numVertices ==> noCollisionAt(vid)
	}

	function method noCollisionAt(src: VertexId): bool
		requires valid0(src) && valid1(vAttr) && valid2(graph) && valid2(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		forall dst :: 0 <= dst < numVertices ==> noCollisionBetween(src, dst)
	}

	function method noCollisionBetween(src: VertexId, dst: VertexId): bool
		requires valid0(src) && valid0(dst) && valid1(vAttr) && valid2(graph) && valid2(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		adjacent(src, dst) && !sent[src, dst] ==> vAttr[src] != vAttr[dst]
	}

	/******************
	 * Helper functions
	 ******************/

	function method active(): bool
		requires valid2(sent)
		reads this`sent, this`numVertices
	{
		exists i, j :: 0 <= i < numVertices && 0 <= j < numVertices && sent[i,j]
	}

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
	{
		graph[src,dst] != 0.0
	}

	predicate valid0(vid: int)
		reads this`numVertices
	{
		0 <= vid < numVertices
	}

	predicate valid1<T> (arr: array<T>)
		reads this`numVertices
	{
		arr != null && arr.Length == numVertices
	}

	predicate valid2<T> (mat: array2<T>)
		reads this`numVertices
	{
		mat != null && mat.Length0 == numVertices && mat.Length1 == numVertices
	}

	predicate inv()
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		!active() ==> correctlyColored()
	}

	method pregel(maxNumIterations: nat) returns (numIterations: nat)
		requires numVertices > 1 && maxNumIterations > 0
		requires valid1(vAttr) && valid2(graph) && valid2(sent) && valid2(msg)
		modifies vAttr, msg, sent
		ensures numIterations <= maxNumIterations ==> correctlyColored()
	{
		var vid := 0;
		while vid < numVertices
		{
			VertexProgram(vid, false);
			vid := vid + 1;
		}
		sent[0,0] := true;
		numIterations := 0;

		witness_for_existence();
		assert active();

		while active() && numIterations <= maxNumIterations
			invariant !active() ==> noCollisions()
		{
			forall i,j | (0 <= i < numVertices && 0 <= j < numVertices)
			{
				sent[i,j] := false;
			}
			var src := 0;
			// invoke SendMessage on each edage
			while src < numVertices
				invariant src <= numVertices
				invariant forall vid :: 0 <= vid < src ==> noCollisionAt(vid)
				invariant numIterations > maxNumIterations ==> noCollisions()
			{
				var dst := 0;
				while dst < numVertices
					invariant dst <= numVertices
					invariant forall vid :: 0 <= vid < dst ==> noCollisionBetween(src, vid);
					invariant forall vid :: 0 <= vid < src ==> noCollisionAt(vid)
				{
					if adjacent(src, dst)
					{
						SendMessage(src, dst, graph[src,dst]);
					}
					assert noCollisionBetween(src, dst);
					dst := dst + 1;
				}
				assert noCollisionAt(src);
				src := src + 1;
			}
			assert noCollisions();

			if exists i, j :: 0 <= i < numVertices && 0 <= j < numVertices && sent[i,j]
			{
				var dst := 0;
				while dst < numVertices
				{
					// Did some vertex send a message to dst?
					if exists src :: 0 <= src < numVertices && sent[src,dst]
					{
						var activated := false;
						var message: Message;
						var src := 0;
						// aggregate the messages sent to dst
						while src < numVertices
						{
							if sent[src,dst]
							{
								if !activated
								{
									// keep the first message as is
									message := msg[src,dst];
									activated := true;
								} else {
									// merge the new message with the old one
									message := MergeMessage(message, msg[src,dst]);
								}
							}
							src := src + 1;
						}
						// update vertex state according to the result of merges
						VertexProgram(dst, message);
					}
					dst := dst + 1;
				}
				assert active();
			}
			assert !(exists i, j :: 0 <= i < numVertices && 0 <= j < numVertices && sent[i,j]) ==> noCollisions();
			numIterations := numIterations + 1;
		}
		assert numIterations <= maxNumIterations ==> !active();		
		assert numIterations <= maxNumIterations ==> noCollisions();
		assert !active() && noCollisions() ==> correctlyColored();
		assert numIterations <= maxNumIterations ==> correctlyColored();
	}

	lemma witness_for_existence()
		requires valid2(sent) && numVertices > 0 && sent[0,0]
		ensures active()
	{}
}