/**
 * This script tries to model and prove correctness of
 * https://github.com/apache/spark/blob/master/graphx/src/main/scala/org/apache/spark/graphx/lib/ConnectedComponents.scala
 */

include "nondet-permutation.dfy"

type VertexId = int
type Message = int
type Color = int
type Weight = real

class PregelGraphColoring
{
	var numVertices: nat;
	var graph: array2<Weight>;
	var vAttr : array<Color>;
	var vMsg : array<Message>;
	var msg : array2<Message>;
	var sent : array2<bool>;

	/**************************************
	 * Beginning of user-supplied functions
	 **************************************/

	method SendMessage(src: VertexId, dst: VertexId, w: Weight)
		requires valid2(graph) && valid1(vAttr) && valid2(sent) && valid2(msg)
		requires valid0(src) && valid0(dst)
		modifies msg, sent
		ensures noCollisionBetween(src, dst)
	{
		if(vAttr[src] < vAttr[dst]) {
			msg[src,dst] := vAttr[src];
			sent[src,dst] := true;
			sent[dst,src] := false;
		} else
		if(vAttr[src] > vAttr[dst]) {
			msg[dst,src] := vAttr[dst];
			sent[dst,src] := true;
			sent[src,dst] := false;
		} else {
			sent[src,dst] := false;
			sent[dst,src] := false;
		}
	}

	function method MergeMessage(a: Message, b: Message): Message { min(a, b) }

	method VertexProgram(vid: VertexId, state: Color, msg: Message) returns (state': Color)
		requires valid0(vid) && valid1(vAttr)
	{
		state' := msg;
	}

	/************************
	 * Correctness assertions
	 ************************/

	function method correctlyColored(): bool
		requires 0 <= numVertices
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		// adjacent vertices have different colors
		correctlyColored'(numVertices)
	}

	function method correctlyColored'(dist: VertexId): bool
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		requires 0 <= dist <= numVertices
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall i,j | 0 <= i < numVertices && 0 <= j < numVertices ::
			connected'(i, j, dist) ==> vAttr[i] == vAttr[j]
	}

	method Validated(maxNumIterations: nat) returns (goal: bool)
		requires numVertices > 0
		requires valid1(vAttr) && valid2(graph) && valid2(sent) && valid2(msg)
		modifies this`numVertices, vAttr, msg, sent
		ensures goal
	{
		var numIterations := Pregel(maxNumIterations);
		goal := numIterations <= maxNumIterations ==> correctlyColored();
	}

	/*******************************
	 * Correctness helper assertions
	 *******************************/

	function method noCollisions(): bool
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall vid | 0 <= vid < numVertices :: noCollisionAt(vid)
	}

	function method noCollisionAt(src: VertexId): bool
		requires valid0(src) && valid1(vAttr) && valid2(graph) && valid2(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		forall dst | 0 <= dst < numVertices :: noCollisionBetween(src, dst)
	}

	function method noCollisionBetween(src: VertexId, dst: VertexId): bool
		requires valid0(src) && valid0(dst) && valid1(vAttr) && valid2(graph) && valid2(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==> vAttr[src] == vAttr[dst]
	}

	function method noCollisions'(srcBound: VertexId, dstBound: VertexId): bool
		requires srcBound <= numVertices && dstBound <= numVertices
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall src,dst | 0 <= src < srcBound && 0 <= dst < dstBound ::
			adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==> vAttr[src] == vAttr[dst]
	}

	lemma ColoringLemma()
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		ensures !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
				&& noCollisions'(numVertices, numVertices) ==> correctlyColored()
	{
		if !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
				&& noCollisions'(numVertices, numVertices)
		{
			ColoringLemma'(numVertices);
		}
	}

	lemma ColoringLemma'(dist: nat)
		requires 0 <= dist <= numVertices
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
		requires !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
		requires noCollisions'(numVertices, numVertices)
		ensures correctlyColored'(dist)
	{
		if dist > 1 { ColoringLemma'(dist - 1); }
	}

	lemma CollisionLemma()
		requires valid1(vAttr) && valid2(graph) && valid2(sent)
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
					invariant forall vid | 0 <= vid < dst ::
						adjacent(src, vid) && !sent[src,vid] && !sent[vid,src] ==> vAttr[src] == vAttr[vid]
				{
					assert noCollisionBetween(src, dst);
					assert adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==> vAttr[src] == vAttr[dst];
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
		requires valid2(sent)
		reads this`sent, this`numVertices
	{
		exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]
	}

	function method min(a: Color, b: Color): Color
	{
		if a >= b then b else a
	}

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
	{
		graph[src,dst] != 0.0
	}

	function method connected(src: VertexId, dst: VertexId): bool
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
	{
		exists dist | 1 <= dist <= numVertices :: connected'(src, dst, dist)
	}

	function method connected'(src: VertexId, dst: VertexId, dist: int): bool
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
		decreases dist
	{
		dist > 0 &&
		if dist == 1
		then
			adjacent(src, dst)
		else
			exists next | 0 <= next < numVertices ::
				adjacent(src, next) && connected'(next, dst, dist - 1)
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

	method Pregel(maxNumIterations: nat) returns (numIterations: nat)
		requires numVertices > 0
		requires valid1(vAttr) && valid2(graph) && valid2(sent) && valid2(msg)
		modifies vAttr, msg, sent
		ensures numIterations <= maxNumIterations ==> correctlyColored()
	{
		var vid := 0;
		while vid < numVertices
		{
			vAttr[vid] := VertexProgram(vid, vAttr[vid], vid);
			vid := vid + 1;
		}
		sent[0,0] := true;
		witness_for_existence();
		assert exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j];

		numIterations := 0;

		while (exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) && numIterations <= maxNumIterations
			invariant !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) ==> noCollisions()
		{
			var vAttr' := new Color[numVertices];
			forall i,j | 0 <= i < numVertices && 0 <= j < numVertices
			{
				sent[i,j] := false;
			}
			var src := 0;
			/* invoke SendMessage on each edage */
			while src < numVertices
				invariant src <= numVertices
				invariant forall vid | 0 <= vid < src :: noCollisionAt(vid)
			{
				var dst := 0;
				while dst < numVertices
					invariant dst <= numVertices
					invariant forall vid | 0 <= vid < src :: noCollisionAt(vid)
					invariant forall vid | 0 <= vid < dst :: noCollisionBetween(src, vid);
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

			if exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]
			{
				var dstCounter := 0;
				var dstIndices := Permutation.Generate(numVertices);
				while dstCounter < numVertices
					//invariant Permutation.IsValid(srcIndices, numVertices)
					invariant Permutation.IsValid(dstIndices, numVertices)
				{
					var dst := dstIndices[dstCounter];
					/* Did some vertex send a message to dst? */
					if exists src | 0 <= src < numVertices :: sent[src,dst]
					{
						var activated := false;
						var message: Message;
						var srcCounter := 0;
						var srcIndices := Permutation.Generate(numVertices);
						/* aggregate the messages sent to dst */
						while srcCounter < numVertices
						{
							var src := srcIndices[srcCounter];
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
							srcCounter := srcCounter + 1;
						}
						/* update vertex state according to the result of merges */
						vAttr[dst] := VertexProgram(dst, vAttr[dst], message);
					}
					dstCounter := dstCounter + 1;
				}
				/* This hack can be removed after bug https://dafny.codeplex.com/workitem/144 is fixed. */
				assume exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j];
			}
			numIterations := numIterations + 1;
		}
		//assert numIterations <= maxNumIterations ==> !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]);
		//assert !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) ==> noCollisions();
		//assert numIterations <= maxNumIterations ==> noCollisions();

		/* noCollisions() and !active() imply correctlyColored() */
		CollisionLemma();
		ColoringLemma();
	}

	lemma witness_for_existence()
		requires valid2(sent) && numVertices > 0 && sent[0,0]
		ensures active()
	{}
}