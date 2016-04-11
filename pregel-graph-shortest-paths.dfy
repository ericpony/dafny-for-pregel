/**
 * This script tries to model and prove correctness of
 * https://github.com/apache/spark/blob/master/graphx/src/main/scala/org/apache/spark/graphx/lib/ShortestPaths.scala
 */

include "nondet-permutation.dfy"

type VertexId = int
type Distance = int
type Message = array<Distance>
type Weight = real

class PregeShortestPaths
{
	var numVertices: nat;
	var graph: array2<Weight>;
	var vAttr : array2<VertexId>;
	var vMsg : array<Message>;
	var msg : array3<Distance>;
	var sent : array2<bool>;

	/**************************************
	 * Beginning of user-supplied functions
	 **************************************/

	method SendMessage(src: VertexId, dst: VertexId, w: Weight)
		requires valid2(graph) && valid2(vAttr) && valid2(sent) && valid3(msg) && valid0(src) && valid0(dst)
		requires MsgMatrixInvariant() && vAttrInvariant()
		modifies msg, sent
		ensures noCollisionBetween(src, dst)
		ensures MsgMatrixInvariant() && vAttrInvariant()
	{
		sent[src,dst] := false;
		sent[dst,src] := false;
		var i := 0;
		while i < numVertices
			invariant i <= numVertices
			invariant (exists j | 0 <= j < i :: vAttr[src,j] > vAttr[dst,j] + 1) ==> sent[dst,src];
			invariant !(exists j | 0 <= j < i :: vAttr[src,j] > vAttr[dst,j] + 1) ==> !sent[dst,src];
		{
			if vAttr[src,i] > vAttr[dst,i] + 1
			{
				forall k | 0 <= k < numVertices {
					msg[dst,src,k] := vAttr[dst,k] + 1;
				}
				sent[dst,src] := true;
				assert vAttr[src,i] > vAttr[dst,i] + 1; // needed by invariant
				break;
			}
			i := i + 1;
		}
		assert sent[dst,src] <==> exists j | 0 <= j < numVertices :: vAttr[src,j] > vAttr[dst,j] + 1;
	}

	method MergeMessage(a: Message, b: Message) returns (c: Message)
		requires valid1(a) && valid1(b)
		ensures fresh(c) && valid1(c)
		ensures forall i | 0 <= i < numVertices :: c[i] == min(a[i], b[i])
	{
		c := new Distance[numVertices];
		forall i | 0 <= i < numVertices {
			c[i] := min(a[i], b[i]);
		}
	}

	method VertexProgram(vid: VertexId, msg: Message)
		requires valid0(vid) && valid2(vAttr) && valid1(msg)
		modifies vAttr
	{
		var i := 0;
		while i < numVertices
		{
			if vid != i {
				vAttr[vid,i] := min(vAttr[vid,i], msg[i]);
			}
			i := i + 1;
		}
	}

	/************************
	 * Correctness assertions
	 ************************/

	function method distVectorConverged(): bool
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		requires vAttrInvariant()
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		distVectorConverged'(numVertices)
	}

	function method distVectorConverged'(dist: nat): bool
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		requires vAttrInvariant()
		requires 0 <= dist <= numVertices
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall i,j | 0 <= i < numVertices && 0 <= j < numVertices ::
			(connected'(i, j, dist) ==> 0 <= vAttr[i,j] <= dist)
	}

	lemma DistanceLemma()
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		requires vAttrInvariant()
		ensures !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
				&& noCollisionsInductive(numVertices, numVertices) ==> distVectorConverged()
	{
		if !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
				&& noCollisionsInductive(numVertices, numVertices)
		{
			DistanceLemma'(numVertices);
		}
	}

	lemma DistanceLemma'(dist: nat)
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		requires 0 <= dist <= numVertices
		requires vAttrInvariant()
		requires !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j])
		requires noCollisionsInductive(numVertices, numVertices)
		//requires noCollisionsInductive'(numVertices, numVertices)
		ensures distVectorConverged'(dist)
	{	
		if dist > 0
		{
			DistanceLemma'(dist - 1);
		}
		/*
		assert forall src,dst | 0 <= src < numVertices && 0 <= dst < numVertices ::
			(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
			forall i | 0 <= i < numVertices ::
				(0 <= vAttr[dst,i] <= numVertices && connected'(dst, i, vAttr[dst,i]) ==>
					connected'(src, i, vAttr[dst,i] + 1)));
		assert distVectorConverged'(0);
		
		if dist > 0
		{
			DistanceLemma'(dist - 1);
			
			var src := 0;
			while src < numVertices
				invariant src <= numVertices
				invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: connected'(i, j, dist) ==> vAttr[i,j] <= dist
				invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: vAttr[i,j] == dist ==> connected'(i, j, dist)
			{
				var dst := 0;
				while dst < numVertices
					invariant dst <= numVertices
					invariant forall j | 0 <= j < dst :: connected'(src, j, dist) ==> vAttr[src,j] <= dist
					invariant forall j | 0 <= j < dst :: vAttr[src,j] == dist ==> connected'(src, j, dist)
				{
					//assert src == dst ==> vAttr[src,dst] == 0;
					//if connected'(src, dst, dist)
					{
						//var v :| 0 <= v < numVertices && adjacent(src, v) && connected'(v, dst, dist - 1);						
						//assert 0 <= vAttr[v,dst] <= dist - 1;
						//assert 0 <= vAttr[src,dst] <= vAttr[v,dst] + 1;
						//assert 0 <= vAttr[src,dst] <= dist;
					}
					//assert connected'(src, dst, dist) ==> vAttr[src,dst] <= dist;
					dst := dst + 1;
				}
				src := src + 1;
			}
		}
		*/
	}

	function method noCollisions'(): bool
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		requires vAttrInvariant()
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall vid | 0 <= vid < numVertices :: noCollisionAt'(vid)
	}

	function method noCollisionAt'(src: VertexId): bool
		requires valid0(src) && valid2(vAttr) && valid2(graph) && valid2(sent)
		requires vAttrInvariant()
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		forall dst | 0 <= dst < numVertices :: noCollisionBetween'(src, dst)
	}

	function method noCollisionBetween'(src: VertexId, dst: VertexId): bool
		requires valid0(src) && valid0(dst) && valid2(vAttr) && valid2(graph) && valid2(sent)
		requires vAttrInvariant()
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
			forall i | 0 <= i < numVertices ::
				(vAttr[dst,i] < numVertices && vAttr[src,i] < numVertices ==> 
					connected'(dst, i, vAttr[dst,i]) ==> connected'(src, i, vAttr[src,i])))
	}

	function method noCollisionsInductive'(srcBound: VertexId, dstBound: VertexId): bool
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		requires srcBound <= numVertices && dstBound <= numVertices
		requires vAttrInvariant()
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall src,dst | 0 <= src < srcBound && 0 <= dst < dstBound ::
			(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
				forall i | 0 <= i < numVertices ::
					(connected'(dst, i, vAttr[dst,i]) ==> connected'(src, i, vAttr[src,i])))
	}

	method Validated(maxNumIterations: nat) returns (goal: bool)
		requires numVertices > 0
		requires valid2(vAttr) && valid2(graph) && valid2(sent) && valid3(msg)
		requires vAttrInvariant() && MsgMatrixInvariant()
		modifies this`numVertices, vAttr, msg, sent
		ensures goal
	{
		var numIterations := Pregel(maxNumIterations);
		goal := numIterations <= maxNumIterations ==> distVectorConverged();
	}

	/*******************************
	 * Correctness helper assertions
	 *******************************/

	function method noCollisions(): bool
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall vid | 0 <= vid < numVertices :: noCollisionAt(vid)
	}

	function method noCollisionAt(src: VertexId): bool
		requires valid0(src) && valid2(vAttr) && valid2(graph) && valid2(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		forall dst | 0 <= dst < numVertices :: noCollisionBetween(src, dst)
	}

	function method noCollisionBetween(src: VertexId, dst: VertexId): bool
		requires valid0(src) && valid0(dst) && valid2(vAttr) && valid2(graph) && valid2(sent)
		reads this`graph, this`sent, this`vAttr, this`numVertices, vAttr
	{
		(src == dst ==> vAttr[src,dst] == 0)
		&&
		(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
			forall i | 0 <= i < numVertices :: vAttr[src,i] <= vAttr[dst,i] + 1)
	}

	function method noCollisionsInductive(srcBound: VertexId, dstBound: VertexId): bool
		requires srcBound <= numVertices && dstBound <= numVertices
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall src,dst | 0 <= src < srcBound && 0 <= dst < dstBound ::
			(src == dst ==> vAttr[src,dst] == 0)
			&&
			(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
				forall i | 0 <= i < numVertices :: vAttr[src,i] <= vAttr[dst,i] + 1)
	}

	lemma CollisionLemma()
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		ensures noCollisions() ==> noCollisionsInductive(numVertices, numVertices)
	{
		if noCollisions()
		{
			var src := 0;
			while src < numVertices
				invariant src <= numVertices
				invariant noCollisionsInductive(src, numVertices)
			{
				var dst := 0;
				assert noCollisionAt(src);
				while dst < numVertices
					invariant dst <= numVertices
					invariant noCollisionsInductive(src, dst)
					invariant forall vid | 0 <= vid < dst ::
					(src == vid ==> vAttr[src,vid] == 0) &&
						(adjacent(src, vid) && !sent[src,vid] && !sent[vid,src] ==>
							forall i | 0 <= i < numVertices :: vAttr[src,i] <= vAttr[vid,i] + 1)
				{
					assert noCollisionBetween(src, dst);
					assert (src == dst ==> vAttr[src,dst] == 0) &&
							(adjacent(src, dst) && !sent[src,dst] && !sent[dst,src] ==>
								forall i | 0 <= i < numVertices :: vAttr[src,i] <= vAttr[dst,i] + 1);
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

	function method min(a: VertexId, b: VertexId): VertexId
	{
		if a >= b then b else a
	}

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
	{
		graph[src,dst] != 0.0
	}

	/* Check if the distance between src and dst is dist. */
	function method hasDistance(src: VertexId, dst: VertexId, dist: int): bool
		requires dist >= 0
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
	{
		if dist == 0 then
			src == dst
		else
			connected'(src, dst, dist) && !connected'(src, dst, dist - 1)
	}

	/* Check if dst is reachable from src. */
	function method connected(src: VertexId, dst: VertexId): bool
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
	{
		exists dist :: 0 <= dist <= numVertices && connected'(src, dst, dist)
	}

	/* Check if dst is reachable from src through a path of length dist. */
	function method connected'(src: VertexId, dst: VertexId, dist: int): bool
		requires dist >= 0
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
		decreases dist
	{
		if dist == 0 then
			src == dst
		else
		if dist == 1 then
			adjacent(src, dst)
		else
			exists next | 0 <= next < numVertices ::
				adjacent(src, next) && connected'(next, dst, dist - 1)
	}

	predicate valid0(vid: VertexId)
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

	predicate valid3<T> (mat: array3<T>)
		reads this`numVertices
	{
		mat != null && mat.Length0 == numVertices && mat.Length1 == numVertices && mat.Length2 == numVertices
	}

	predicate isNonnegative (arr: array<Distance>)
		requires arr != null && arr.Length == numVertices
		reads this`numVertices, arr
	{
		forall i | 0 <= i < numVertices :: arr[i] >= 0
	}

	predicate vAttrInvariant0()
		requires valid2(vAttr)
		reads this`numVertices, this`vAttr
	{
		forall i | 0 <= i < numVertices :: vAttr[i,i] == 0
	}

	predicate vAttrInvariant()
		requires valid2(vAttr)
		reads this`numVertices, this`vAttr
	{
		(forall i | 0 <= i < numVertices :: vAttr[i,i] == 0)
		&&
		(forall i,j | 0 <= i < numVertices && 0 <= j < numVertices :: vAttr[i,j] >= 0)
	}

	predicate MsgMatrixInvariant()
		requires valid3(msg)
		reads this`numVertices, this`msg
	{
		true
		//forall i,j | 0 <= i < numVertices && 0 <= j < numVertices ::
		//	valid1(msg[i,j]) // && isNonnegative(msg[i,j])
	}

	method Pregel(maxNumIterations: nat) returns (numIterations: nat)
		requires numVertices > 0
		requires valid2(vAttr) && valid2(graph) && valid2(sent) && valid3(msg)
		requires vAttrInvariant() && MsgMatrixInvariant()
		modifies vAttr, msg, sent
		ensures vAttrInvariant()
		ensures numIterations <= maxNumIterations ==> distVectorConverged()
	{
		var src := 0;
		while src < numVertices
			invariant src <= numVertices
			invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: vAttr[i,j] == if i == j then 0 else numVertices + 1
		{
			var dst := 0;
			while dst < numVertices
				invariant dst <= numVertices
				invariant forall j | 0 <= j < dst :: vAttr[src,j] == if src == j then 0 else numVertices + 1
				invariant forall i,j | 0 <= i < src && 0 <= j < numVertices :: vAttr[i,j] == if i == j then 0 else numVertices + 1
			{
				vAttr[src,dst] := if src == dst then 0 else numVertices + 1;
				dst := dst + 1;
			}
			src := src + 1;
		}
		sent[0,0] := true;
		assert sent[0,0]; // needed by the following assertion
		assert exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j];

		assert noCollisions'();

		numIterations := 0;

		while (exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) && numIterations <= maxNumIterations
			invariant !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) ==> noCollisions()
			//invariant !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) ==> noCollisions'()
		{
			forall i,j | 0 <= i < numVertices && 0 <= j < numVertices
			{
				sent[i,j] := false;
			}
			var src := 0;
			
			/* invoke SendMessage on each edage */
			while src < numVertices
				invariant src <= numVertices
				invariant forall vid | 0 <= vid < src :: noCollisionAt(vid)
				//invariant forall vid | 0 <= vid < src :: noCollisionAt'(vid)
			{
				var dst := 0;
				while dst < numVertices
					invariant dst <= numVertices
					invariant vAttrInvariant()
					invariant forall vid | 0 <= vid < src :: noCollisionAt(vid)
					invariant forall vid | 0 <= vid < dst :: noCollisionBetween(src, vid)
				{
					if adjacent(src, dst)
					{
						SendMessage(src, dst, graph[src,dst]);
						//assert noCollisionBetween(src, dst);
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
					//invariant noCollisions'()
					invariant Permutation.IsValid(dstIndices, numVertices)
				{
					var dst := dstIndices[dstCounter];
					/* Did some vertex send a message to dst? */
					if exists src | 0 <= src < numVertices :: sent[src,dst]
					{
						var activated := false;
						var message: Message := new Distance[numVertices];
						var srcCounter := 0;
						var srcIndices := Permutation.Generate(numVertices);
						/* aggregate the messages sent to dst */
						while srcCounter < numVertices
							invariant valid1(message)
							invariant MsgMatrixInvariant()
							//invariant noCollisions'()
							invariant Permutation.IsValid(srcIndices, numVertices)
							invariant Permutation.IsValid(dstIndices, numVertices)
						{
							var src := srcIndices[srcCounter];
							if sent[src,dst]
							{
								var message' := new Distance[numVertices];
								forall i | 0 <= i < numVertices {
									message'[i] := msg[src,dst,i];
								}
								if !activated
								{
									/* keep the first message as is */
									message := message';
									activated := true;
								} else {
									/* merge the new message with the old one */
									message := MergeMessage(message, message');
								}
							}
							srcCounter := srcCounter + 1;
						}
						/* update vertex state according to the result of merges */
						VertexProgram(dst, message);
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
		//assert numIterations <= maxNumIterations ==> noCollisions'();

		/* noCollisions() and !active() imply distVectorConverged() */
		CollisionLemma();
		DistanceLemma();
	}
}