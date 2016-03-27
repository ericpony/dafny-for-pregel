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
		requires msg != null && msg.Length0 > src && msg.Length1 > dst
		requires sent != null && sent.Length0 > src && sent.Length1 > dst
		requires vAttr != null && vAttr.Length > src && vAttr.Length > dst
		requires src >= 0 && dst >= 0
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

	method vprog(vid: VertexId, msg: Message)
		requires vid >= 0
		requires vAttr != null && vAttr.Length > 1 && vAttr.Length > vid
		modifies vAttr
	{
		if(msg == true)
		{
			// choose a different color nondeterministically
			var newColor :| newColor != vAttr[vid] && newColor >= 0 && newColor < vAttr.Length;
			vAttr[vid] := newColor;
		}
	}

	function method vprog2(vid: VertexId, msg: Message, attr: Color): Color
		requires vAttr != null && vAttr.Length > 1 && vAttr.Length > vid
		reads this`vAttr
	{
		// function cannot return a nondeterministic value
		// var a :| a != attr && a >= 0 && a < vAttr.Length; a
		if msg then (attr + 1) % vAttr.Length else attr
	}

	/***********************
	 * Correctness assertion
	 ***********************/

	function method Invariant(): bool
		requires graph != null && sent != null && vAttr != null
		requires vAttr.Length == graph.Length0 == graph.Length1
		reads this`graph, this`vAttr, this`sent, vAttr
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
		requires sent != null
		reads this`sent
	{
		exists i, j :: 0 <= i < sent.Length0 && 0 <= j < sent.Length1 && sent[i,j]
	}

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires graph != null && 0 <= src < graph.Length0 && 0 <= dst < graph.Length1
		reads this`graph
	{
		graph[src,dst] > 0.0
	}

	method Pregel()
		requires numVertices > 1
		requires vAttr != null && vAttr.Length == numVertices
		requires graph != null && graph.Length0 == numVertices && graph.Length1 == numVertices
		requires sent != null && sent.Length0 == numVertices && sent.Length1 == numVertices
		requires msg != null && msg.Length0 == numVertices && msg.Length1 == numVertices
		requires forall i,j :: (0 <= i < numVertices && 0 <= j < numVertices) ==> graph[i,j] >= 0.0
		modifies vAttr, msg, sent
	{
		//forall i: VertexId | (0 <= i < numVertices) { vAttr[i] := vprog2(i, false, vAttr[i]); }
		var vid := 0;
		while vid < numVertices
		{
			vprog(vid, false);
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
						vprog(dst, message);
						// vAttr[dst] := vprog2(dst, message, vAttr[dst]);
					}
					dst := dst + 1;
				}
			}
		}
		// A correct coloring is obtained after the loop exits
		assert(Invariant());
	}
}