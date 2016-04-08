type VertexId = int
type Message = bool
type Color = int
type Weight = real

class GraphConnectivity
{
	var numVertices: int;
	var graph: array2<Weight>;

	method IsConnected() returns (isConnected: bool)
		requires numVertices > 0
		requires valid2(graph)
		ensures graph == old(graph) && numVertices == old(numVertices)
		ensures numVertices == old(numVertices)
		modifies this`graph, this`numVertices
	{
		var a,b := ConnectivityPartitionOf(0);
		isConnected := a == set vid: VertexId | 0 <= vid < numVertices;
	}
	/**
	 * Given a vertex src, compute a partition {A,B} of the vertex set, such that
	 * 1) src is in A,
	 * 2) src is connected with all other vertices in A, and
	 * 3) src is not connected with all the vertices in B.
	 */
	method ConnectivityPartitionOf(src: VertexId) returns (A: set<VertexId>, B: set<VertexId>)
		requires valid2(graph) && valid0(src)
		ensures graph == old(graph) && numVertices == old(numVertices)
		ensures forall vid :: valid0(vid) && vid in A ==> vid == src || connected(src, vid)
		ensures forall vid :: valid0(vid) && vid in B ==> vid != src && !connected(src, vid)
		ensures forall vid :: valid0(vid) ==> vid in A + B && vid in A + B ==> valid0(vid)
		ensures A * B == {}
		modifies this`graph, this`numVertices
	{
		A := {};
		B := {};
		var vid := 0;
		while vid < numVertices
			invariant forall vid :: vid in A ==> valid0(vid)
			invariant forall vid :: vid in A ==> vid == src || connected(src, vid)
			invariant forall vid :: vid in B ==> valid0(vid)
			invariant forall vid :: vid in B ==> !connected(src, vid)
			invariant forall v :: 0 <= v < vid ==> valid0(v)
			invariant forall v :: 0 <= v < vid ==> v == src || connected(src, v) ==> v in A
			invariant forall v :: 0 <= v < vid ==> v != src && !connected(src, v) ==> v in B
			invariant forall v :: v >= vid ==> v !in B && v !in B
			invariant A !! B
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