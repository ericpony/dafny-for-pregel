/**
 * This script tries to model and prove correctness of
 * https://github.com/apache/spark/blob/master/graphx/src/main/scala/org/apache/spark/graphx/lib/ShortestPaths.scala
 */

include "nondet-permutation.dfy"
include "merge-disjoint-maps.dfy"

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
	var msg : array2<Message>;
	var sent : array2<bool>;

	/**************************************
	 * Beginning of user-supplied functions
	 **************************************/

	method SendMessage(src: VertexId, dst: VertexId, w: Weight)
		requires valid2(graph) && valid2(vAttr) && valid2(sent) && valid2(msg) && valid0(src) && valid0(dst)
		requires MsgMatrixInvariant() && vAttrInvariant0()
		modifies msg, sent
		ensures noCollisionBetween(src, dst)
		ensures MsgMatrixInvariant() && vAttrInvariant0()
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
				var msg' := new Distance[numVertices];
				forall k | 0 <= k < numVertices {
					msg'[k] := vAttr[dst,k] + 1;
				}
				msg[dst,src] := msg';
				sent[dst,src] := true;
				assert vAttr[src,i] > vAttr[dst,i] + 1; // needed by the invariant
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
		requires vAttrInvariant0()
		modifies vAttr
		ensures vAttrInvariant0()
	{
		var i := 0;
		while i < numVertices
			invariant vAttrInvariant0()
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
		// adjacent vertices have different DistMaps
		distVectorConverged'(numVertices)
	}

	function method distVectorConverged'(dist: nat): bool
		requires valid2(vAttr) && valid2(graph) && valid2(sent)
		requires vAttrInvariant()
		requires 0 <= dist <= numVertices
		reads vAttr, this`graph, this`vAttr, this`sent, this`numVertices
	{
		forall src,next,dst | 0 <= src < numVertices && 
			0 <= next < numVertices && 
			0 <= dst < numVertices && adjacent(src, next) ::
			connected'(src, dst, dist) ==> hasDistance(src, dst, vAttr[src,dst])
	}

	method Validated(maxNumIterations: nat) returns (goal: bool)
		requires numVertices > 0
		requires valid2(vAttr) && valid2(graph) && valid2(sent) && valid2(msg)
		requires vAttrInvariant() && MsgMatrixInvariant()
		modifies this`numVertices, vAttr, msg, sent
		// TODO: prove goal
		//ensures goal
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

	function method noCollisions'(srcBound: VertexId, dstBound: VertexId): bool
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
		exists dist :: 1 <= dist <= numVertices && connected'(src, dst, dist)
	}

	/* Check if dst is reachable from src through a path of length dist. */
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
		requires valid2(msg)
		reads this`numVertices, this`msg
	{
		forall i,j | 0 <= i < numVertices && 0 <= j < numVertices :: 
			valid1(msg[i,j]) // && isNonnegative(msg[i,j])
	}

	method Pregel(maxNumIterations: nat) returns (numIterations: nat)
		requires numVertices > 0
		requires valid2(vAttr) && valid2(graph) && valid2(sent) && valid2(msg)
		requires vAttrInvariant() && MsgMatrixInvariant()
		modifies vAttr, msg, sent
		ensures vAttrInvariant()
		//ensures numIterations <= maxNumIterations ==> distVectorConverged()
	{
		var i := 0;
		while i < numVertices
		{
			var j := 0;
			while j < numVertices
			{
				if i == j {
					vAttr[i,j] := 0;
				} else {
					vAttr[i,j] := numVertices;
				}
				j := j + 1;
			}
			i := i + 1;
		}
		sent[0,0] := true;
		assert sent[0,0]; // needed by the following assertion
		assert exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j];

		numIterations := 0;

		while (exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) && numIterations <= maxNumIterations
			invariant !(exists i,j | 0 <= i < numVertices && 0 <= j < numVertices :: sent[i,j]) ==> noCollisions()
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
			{
				var dst := 0;
				while dst < numVertices
					invariant dst <= numVertices
					invariant vAttrInvariant()
					invariant forall vid | 0 <= vid < src :: noCollisionAt(vid)
					invariant forall vid | 0 <= vid < dst :: noCollisionBetween(src, vid);
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
							invariant Permutation.IsValid(srcIndices, numVertices)
							invariant Permutation.IsValid(dstIndices, numVertices)
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
		//assert numIterations <= maxNumIterations ==> noCollisions();

		/* noCollisions() and !active() imply distVectorConverged() */
		CollisionLemma();
	}
}