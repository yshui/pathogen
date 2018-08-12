/// Internal utility functions/algorithms of pathogen
module pathogen.utils;

private struct State {
	uint[] ord;
	uint[] P;
	uint[] S;
	uint[] scc;
	uint id, sccid;
	this(size_t nnode) {
		id = 1;
		sccid = 1;
		ord = new uint[nnode];
		scc = new uint[nnode];
	}
}
private void scc(uint v, const(int[])[] g, ref State s) {
	import std.algorithm;
	s.ord[v] = s.id;
	s.id++;
	s.S ~= v;
	s.P ~= v;

	foreach(w; g[v]) {
		if (s.ord[w] == 0)
			scc(w, g, s);
		else if (s.scc[w] == 0) {
			while (s.ord[s.P[$-1]] > s.ord[w])
				s.P.length--;
		}
	}

	if (v == s.P[$-1]) {
		uint top;
		do {
			top = s.S[$-1];
			s.scc[top] = s.sccid;
			s.S.length--;
		} while (top != v);
		s.sccid++;
		s.P.length--;
	}
}

package uint[] scc(const(int[])[] g) {
	auto s = State(g.length);
	foreach(uint i; 0..cast(uint)g.length)
		if (s.ord[i] == 0)
			scc(i, g, s);
	return s.scc;
}

unittest {
	int[][] g = [
		[1, 3],
		[2],
		[0, 6],
		[5],
		[3],
		[6],
		[4],
		[5, 10],
		[7],
		[8],
		[9, 11],
		[9]
	];
	import std.algorithm;
	assert(g.scc.equal([2, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 3]));
}
