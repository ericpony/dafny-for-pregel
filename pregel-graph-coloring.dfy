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
	{
		if vAttr[src] != vAttr[dst] {
			msg[src, dst] := true;
			sent[src, dst] := true;
		}
	}

	function method MergeMessage(a: Message, b: Message): bool { a || b }

	method VertexProgram(vid: VertexId, msg: Message)
		requires valid0(vid) && valid1(vAttr)
		requires vAttr.Length > 1 // so that we can use a different color
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

	predicate Validated()
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		// Adjacent vertices have different colors after the algorithm terminates.
		forall i,j :: 0 <= i < vAttr.Length && 0 <= j < vAttr.Length ==> 
			adjacent(i, j) ==> vAttr[i] != vAttr[j]
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
		!active() ==> Validated()
	}

	method pregel(maxNumIterations: nat)
		requires numVertices > 1
		requires valid1(vAttr) && valid2(graph) && valid2(sent) && valid2(msg)
		modifies vAttr, msg, sent
		ensures inv()
	{
		var vid := 0;
		while vid < numVertices
		{
			VertexProgram(vid, false);
			vid := vid + 1;
		}
		sent[0,0] := true;
		var numIterations := 0;

		while active() && numIterations <= maxNumIterations
			//TODO: Prove invariant inv()
		{
			numIterations := numIterations + 1;
			forall i,j | (0 <= i < numVertices && 0 <= j < numVertices)
			{
				sent[i,j] := false;
			}
			var src := 0;
			// invoke SendMessage on each edage
			while src < numVertices
			{
				var dst := 0;
				while dst < numVertices
				{
					if adjacent(src, dst)
					{
						SendMessage(src, dst, graph[src,dst]);
					}
					dst := dst + 1;
				}
				src := src + 1;
			}
			// Has there at least one message been sent?
			if active()
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
			}
		}
	}
}