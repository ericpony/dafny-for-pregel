include "nondet-permutation.dfy"

type VertexId = int
type Weight = real

class MatrixGraph
{
	var numVertices: int;
	var graph: array2<Weight>;

	constructor (matrix: array2<Weight>)
		requires matrix != null
		requires matrix.Length0 == matrix.Length1
		modifies this
	{
		graph := matrix;
		numVertices := matrix.Length0;
	}

	function isConnectedGraph(): bool
		requires valid2(graph)
		reads this`graph, this`numVertices
	{
		isConnected(set vid | 0 <= vid < numVertices)
	}

	function isConnected(vertices: set<VertexId>): bool
		requires forall vid | vid in vertices :: 0 <= vid < numVertices
		requires valid2(graph)
		reads this`graph, this`numVertices
	{
		forall v,u | {v,u} < vertices && v != u :: connected(v, u)
	}

	method ConnectedComponentDecomposition() returns (ccs: set<set<VertexId>>)
		requires valid2(graph)
		modifies this`graph, this`numVertices
		// TODO: prove the following post-condition
		//ensures forall c | c in ccs :: isConnected(c)
	{
		ccs := {};
		var vertices := set vid | 0 <= vid < numVertices;
		var marked := {};
		while marked < vertices
			invariant graph == old(graph) && numVertices == old(numVertices)
			decreases |vertices| - |marked|
		{
			Permutation.CardinalityOrderingLemma(marked, vertices);
			var src :| 0 <= src < numVertices && src !in marked;
			var reachable,unreachable := PartitionByReachability(src);
			ghost var marked' := marked;
			marked := marked + reachable;
			ccs := ccs + {reachable};
			Permutation.CardinalityOrderingLemma(marked', marked);
		}
	}

	/**
	 * Given a vertex src, compute a partition {A,B} of the vertex set, such that
	 * 1) src is in A,
	 * 2) src can reach all other vertices in A, and
	 * 3) src can not reach any vertices in B.
	 */
	method PartitionByReachability(src: VertexId) returns (A: set<VertexId>, B: set<VertexId>)
		requires valid2(graph) && valid0(src)
		ensures graph == old(graph) && numVertices == old(numVertices)
		ensures forall vid | 0 <= vid < numVertices && vid in A :: vid == src || connected(src, vid)
		ensures forall vid | 0 <= vid < numVertices && vid in B :: vid != src && !connected(src, vid)
		ensures A + B == set vid | 0 <= vid < numVertices
		ensures A * B == {}
		// TODO: prove the following post-condition
		//ensures isConnected(A)
		modifies this`graph, this`numVertices
	{
		A := {};
		B := {};
		var vid := 0;
		while vid < numVertices
			invariant vid <= numVertices
			invariant forall v | v in A :: 0 <= v < numVertices
			invariant forall v | v in A :: v == src || connected(src, v)
			invariant forall v | v in B :: 0 <= v < numVertices
			invariant forall v | v in B :: v != src && !connected(src, v)
			invariant forall v | 0 <= v < vid :: v == src || connected(src, v) ==> v in A
			invariant forall v | 0 <= v < vid :: v != src && !connected(src, v) ==> v in B
			invariant forall v | v >= vid :: v !in B && v !in B
			invariant A + B == set v | 0 <= v < vid
		{
			if(vid == src || connected(src, vid))
			{
				A := A + {vid};
			} else {
				B := B + {vid};
			}
			vid := vid + 1;
		}
	}

	/******************
	 * Helper functions
	 ******************/

	function method adjacent(src: VertexId, dst: VertexId): bool
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
	{
		graph[src,dst] != 0.0
	}

	/* Check if the distance between src and dst is dist. */
	function method hasDistance(src: VertexId, dst: VertexId, dist: nat): bool
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

	function method isPathBetween(path: seq<VertexId>, src: VertexId, dst: VertexId): bool
		requires forall vid | vid in path :: valid0(vid)
		requires valid2(graph) && valid0(src) && valid0(dst)
		reads this`graph, this`numVertices
	{
		if |path| == 0 then
			false
		else
		if |path| == 1 then
			path[0] == src == dst
		else 
			path[0] == src && adjacent(src, path[1]) && isPathBetween(path[1..], path[1], dst)
	}


	function valid0(vid: VertexId): bool
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

	lemma ConnectivityLemma2(v1: VertexId, v2: VertexId, v3: VertexId, dist: nat)
		requires 1 <= dist < numVertices
		requires valid2(graph) && valid0(v1) && valid0(v2) && valid0(v3)
		ensures adjacent(v1, v2) && connected'(v2, v3, dist) ==> connected(v1, v3)
	{
		ConnectivityLemma2'(v1, v3, dist + 1);
	}

	lemma ConnectivityLemma2'(src: VertexId, dst: VertexId, dist: nat)
		requires 1 <= dist <= numVertices
		requires valid2(graph) && valid0(src) && valid0(dst)
		ensures connected'(src, dst, dist) ==> connected(src, dst)
	{}
}