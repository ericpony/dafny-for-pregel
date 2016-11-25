type VertexId = int
type Message = bool
type Color = int
type Weight = real

class PregelGraphColoring
{
	var numVertices: int;
	var graph: array2<Weight>;
	var vAttr : array<Color>;
	var vMsg : array<Message>;
	var msg : array2<Message>;
	var sent : array2<bool>;

	/**************************************
	 * Beginning of user-supplied functions
	 **************************************/

	method SendMessage(src: VertexId, dst: VertexId, w: Weight)
		requires isArray(vAttr) && isMatrix(sent) && isMatrix(graph) && isMatrix(msg)
		requires isVertex(src) && isVertex(dst)
		requires forall vid :: 0 <= vid < src ==> noCollisionAt(vid)
		requires forall vid :: 0 <= vid < dst ==> noCollisionBetween(src, vid);
		modifies msg, sent
		ensures sent[src, dst] ==> vAttr[src] == vAttr[dst];
		ensures !sent[src, dst] ==> vAttr[src] != vAttr[dst];
		ensures forall vid :: 0 <= vid < src ==> noCollisionAt(vid)
		ensures forall vid :: 0 <= vid < dst ==> noCollisionBetween(src, vid);
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

	method VertexProgram(vid: VertexId, state: Color, msg: Message) returns (state': Color)
		requires isVertex(vid) && isArray(vAttr)
	{
		if msg == true {
			// choose a different color nondeterministically
			var color :| color >= 0 && color < vAttr.Length;
			state' := color;
		} else {
			state' := state;
		}
	}

	/************************
	 * Correctness assertions
	 ************************/

	function method correctlyColored(): bool
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices, graph, sent
	{
		// adjacent vertices have different colors
		forall i,j :: 0 <= i < numVertices && 0 <= j < numVertices ==>
			adjacent(i, j) ==> vAttr[i] != vAttr[j]
	}

	/*******************************
	 * Correctness helper assertions
	 *******************************/

	method Validated(maxNumIterations: nat) returns (goal: bool)
		requires numVertices > 1 && maxNumIterations > 0
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent) && isMatrix(msg)
		modifies this`numVertices, vAttr, msg, sent
		ensures goal
	{
		var numIterations := Pregel(maxNumIterations);
		goal := numIterations <= maxNumIterations ==> correctlyColored();
	}

	function method noCollisions(): bool
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices, graph, sent
	{
		forall vid :: 0 <= vid < numVertices ==> noCollisionAt(vid)
	}

	function method noCollisionAt(src: VertexId): bool
		requires isVertex(src) && isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr, graph, sent
	{
		forall dst :: 0 <= dst < numVertices ==> noCollisionBetween(src, dst)
	}

	function method noCollisionBetween(src: VertexId, dst: VertexId): bool
		requires isVertex(src) && isVertex(dst) && isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr, graph, sent
	{
		adjacent(src, dst) && !sent[src, dst] ==> vAttr[src] != vAttr[dst]
	}

	function method noCollisions'(srcBound: VertexId, dstBound: VertexId): bool
		requires srcBound <= numVertices && dstBound <= numVertices
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices, graph, sent
	{
		forall src,dst :: 0 <= src < srcBound && 0 <= dst < dstBound ==>
			(adjacent(src, dst) && !sent[src, dst] ==> vAttr[src] != vAttr[dst])
	}

	lemma CollisionLemma()
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent)
		ensures noCollisions() ==> noCollisions'(numVertices, numVertices)
	{
		if noCollisions()
		{
			var src := 0;
			while src < numVertices
				invariant src <= numVertices
				invariant noCollisions'(src, numVertices)
			{
				var dst := 0;
				assert noCollisionAt(src);
				while dst < numVertices
					invariant dst <= numVertices
					invariant noCollisions'(src, dst)
					invariant forall vid :: 0 <= vid < dst ==>
						(adjacent(src, vid) && !sent[src, vid] ==> vAttr[src] != vAttr[vid])
				{
					assert noCollisionBetween(src, dst);
					assert adjacent(src, dst) && !sent[src, dst] ==> vAttr[src] != vAttr[dst];
					dst := dst + 1;
				}
				src := src + 1;
			}
		}
	}

	/******************
	 * Helper functions
	 ******************/

	function method active(): bool
		requires isMatrix(sent)
		reads this`sent, sent, this`numVertices
	{
		exists i,j :: 0 <= i < numVertices && 0 <= j < numVertices && sent[i,j]
	}

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires isMatrix(graph) && isVertex(src) && isVertex(dst)
		reads this`graph, this`numVertices, graph
	{
		graph[src,dst] != 0.0
	}

	predicate isVertex(vid: int)
		reads this`numVertices
	{
		0 <= vid < numVertices
	}

	predicate isArray<T> (arr: array<T>)
		reads this`numVertices
	{
		arr != null && arr.Length == numVertices
	}

	predicate isMatrix<T> (mat: array2<T>)
		reads this`numVertices
	{
		mat != null && mat.Length0 == numVertices && mat.Length1 == numVertices
	}

	method Pregel(maxNumIterations: nat) returns (numIterations: nat)
		requires numVertices > 1 && maxNumIterations > 0
		requires isArray(vAttr) && isMatrix(graph) && isMatrix(sent) && isMatrix(msg)
		modifies vAttr, msg, sent
		ensures numIterations <= maxNumIterations ==> correctlyColored()
	{
		var vid := 0;
		while vid < numVertices
		{
			vAttr[vid] := VertexProgram(vid, vAttr[vid], false);
			vid := vid + 1;
		}
		sent[0,0] := true;
		witness_for_existence();
		assert exists i, j :: 0 <= i < numVertices && 0 <= j < numVertices && sent[i,j];

		numIterations := 0;

		while active() && numIterations <= maxNumIterations
			invariant !active() ==> noCollisions()
		{
			forall i,j | 0 <= i < numVertices && 0 <= j < numVertices
			{
				sent[i,j] := false;
			}
			var src := 0;
			/* invoke SendMessage on each edge */
			while src < numVertices
				invariant src <= numVertices
				invariant forall vid :: 0 <= vid < src ==> noCollisionAt(vid)
				invariant numIterations > maxNumIterations ==> noCollisions()
			{
				var dst := 0;
				while dst < numVertices
					invariant dst <= numVertices
					invariant forall vid :: 0 <= vid < src ==> noCollisionAt(vid)
					invariant forall vid :: 0 <= vid < dst ==> noCollisionBetween(src, vid);
				{
					if adjacent(src, dst)
					{
						SendMessage(src, dst, graph[src,dst]);
					}
					//assert noCollisionBetween(src, dst);
					dst := dst + 1;
				}
				//assert noCollisionAt(src);
				src := src + 1;
			}
			assert noCollisions();

			/* Did some vertex send a message to dst? */
			if active()
			{
				//var src',dst' :| 0 <= src' < numVertices && 0 <= dst' < numVertices && sent[src',dst'];
				var dst := 0;
				while dst < numVertices
					invariant active()
				{
					var activated := false;
					var message: Message;
					var src := 0;
					/* aggregate the messages sent to dst */
					while src < numVertices
						invariant active()
					{
						if sent[src,dst]
						{
							if !activated
							{
								/* keep the first message as is */
								message := msg[src,dst];
								activated := true;
							} else {
								/* merge the new message with the old one */
								message := MergeMessage(message, msg[src,dst]);
							}
						}
						src := src + 1;
					}
					/* update vertex state according to the result of merges */
					vAttr[dst] := VertexProgram(dst, vAttr[dst], message);
					dst := dst + 1;
				}
			}
			numIterations := numIterations + 1;
		}
		CollisionLemma();
	}

	lemma witness_for_existence()
		requires isMatrix(sent) && numVertices > 0 && sent[0,0]
		ensures active()
	{}
}