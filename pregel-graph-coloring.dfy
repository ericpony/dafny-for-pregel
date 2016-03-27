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
		if(vAttr[src] != vAttr[dst]) {
			msg[src, dst] := true;
			sent[src, dst] := true;
		}
	}

	function method MergeMessage(a: Message, b: Message): Message
	{
		a || b
	}

	method VertexProgram(vid: VertexId, msg: Message)
		requires valid0(vid) && valid1(vAttr)
		requires vAttr.Length > 1 // so that we can use a different color
		modifies vAttr
	{
		if(msg == true)
		{
			// choose a different color nondeterministically
			var newColor :| newColor != vAttr[vid] && newColor >= 0 && newColor < vAttr.Length;
			vAttr[vid] := newColor;
		}
	}

	function method VertexProgram_v2(vid: VertexId, msg: Message, attr: Color): Color
		requires valid0(vid) && valid1(vAttr)
		requires vAttr.Length > 1 // so that we can use a different color
		reads this`vAttr, this`numVertices
	{
		// function cannot return a nondeterministic value
		// var a :| a != attr && a >= 0 && a < vAttr.Length; a
		if msg then (attr + 1) % vAttr.Length else attr
	}

	/***********************
	 * Correctness assertion
	 ***********************/

	function method Invariant(): bool
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		// After the Pregel loop terminates, adjacent vertices will have different colors.
		!active() ==>
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

	function valid0(vid: int): bool
		reads this`numVertices
	{
		0 <= vid < numVertices
	}

	function valid1<T> (arr: array<T>): bool
		reads this`numVertices
	{
		arr != null && arr.Length == numVertices
	}

	function valid2<T> (mat: array2<T>): bool
		reads this`numVertices
	{
		mat != null && mat.Length0 == numVertices && mat.Length1 == numVertices
	}

	method Pregel()
		requires numVertices > 1
		requires valid1(vAttr) && valid2(graph) && valid2(sent) && valid2(msg)
		//requires forall i,j :: (0 <= i < numVertices && 0 <= j < numVertices) ==> graph[i,j] >= 0.0
		modifies vAttr, msg, sent
	{
		//forall i: VertexId | (0 <= i < numVertices) { vAttr[i] := VertexProgram_v2(i, false, vAttr[i]); }
		var vid := 0;
		while vid < numVertices
		{
			VertexProgram(vid, false);
			vid := vid + 1;
		}
		sent[0,0] := true;

		while active()
			invariant Invariant()
		{
			forall i,j | (0 <= i < numVertices && 0 <= j < numVertices)
			{
				sent[i,j] := false;
			}
			var src := 0;
			var dst := 0;
			// invoke SendMessage on each edage
			while src < numVertices
			{
				while dst < numVertices
				{
					if(adjacent(src, dst))
					{
						SendMessage(src, dst, graph[src,dst]);
					}
					dst := dst + 1;
				}
				src := src + 1;
			}
			// Has there at least one message been sent?
			if(active())
			{
				dst := 0;
				while dst < numVertices
				{
					// Did some vertex send a message to dst?
					if(exists src :: 0 <= src < numVertices && sent[src,dst])
					{
						var activated := false;
						var message : Message;
						var src := 0;
						// aggregate the messages sent to dst
						while src < numVertices
						{
							if(sent[src,dst])
							{
								if(!activated)
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
						// vAttr[dst] := VertexProgram_v2(dst, message, vAttr[dst]);
					}
					dst := dst + 1;
				}
			}
		}
		// A correct coloring is obtained after the loop exits.
		assert(Invariant());
	}
}