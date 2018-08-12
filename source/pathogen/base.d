module pathogen.base;
import std.range;
import std.meta;
import std.traits;
import std.exception;
import std.typecons : Nullable, Tuple;
import std.experimental.allocator;

alias Void = void[0];

package struct _VoidError { }
alias VoidError = _VoidError[0];

package struct _VoidT { }
alias VoidT = _VoidT[0];

// Parser Generator State
package struct PGS {
	bool[] matchesEmpty;
	bool[] leftRecursive;
}

private alias asPointer(T) = T*;

private final struct MemoEntry(T, R, bool recursive = false) {
	Result!(R, T) ans;
	static if (recursive) {
		ulong index;
		ulong lowlink;
		bool tentative; // == onStack in Tarjan SCC
		this(Result!(R, T) a, ulong i) {
			index = i;
			ans = a;
			lowlink = index;
			tentative = true;
		}
	} else {
		this(Result!(R, T) a, ulong) {
			ans = a;
		}
	}
}

private template MemoEntryEx(T, R, PGS pgs, Parsers...) {
	enum id = staticIndexOf!(T, Parsers);
	static assert(id != -1);
	alias MemoEntryEx = MemoEntry!(T, R, pgs.leftRecursive[id]);
}

struct Memo(R, Alloc, PGS pgs, Parsers...) if (isRangeAcceptable!R){
	private alias ETypes = staticMap!(ApplyRight!(MemoEntryEx, R, pgs, Parsers), Parsers);
	private alias EPtrTypes = staticMap!(asPointer, ETypes);
	private struct Stack {
		uint[Parsers.length] stack;
		ulong top;
		void push(uint x) { stack[top++] = x; }
		uint pop() in(top > 0) { return stack[--top]; }
		uint front() in(top > 0) { return stack[top-1]; }
	}
	Tuple!EPtrTypes[] m;
	Stack[] stack;
	Alloc alloc;
	ulong index = 1; // current parser index, increment for every parser call
	size_t offset;
	uint parser_id;

	@safe auto update_offset(size_t i) {
		auto ooff = offset;
		offset = i;
		return ooff;
	}

	@safe auto update_offset(R i) { return update_offset(i.offset); }

	@safe auto update_parser(uint nparser) {
		auto oparser = parser_id;
		parser_id = nparser;
		return oparser;
	}

	@safe auto update_parser(P)() {
		enum id = staticIndexOf!(P, Parsers);
		static assert(id != -1);
		return update_parser(id);
	}

	@safe auto get(P)(R i) {
		enum id = staticIndexOf!(P, Parsers);
		static assert(id != -1);
		return m[i.offset][id];
	}

	@safe auto get_next_offset(R i, uint id) {
		final switch(id) {
			foreach(j, P; Parsers) {
			case j:
				return m[i.offset][j].ans.next_offset;
			}
		}
	}

	@trusted auto push(P)(R i) {
		enum id = staticIndexOf!(P, Parsers);
		static assert(id != -1);
		if (i.offset >= stack.length)
			alloc.expandArray(stack, stack.length);
		stack[i.offset].push(id);
	}

	@safe auto front(R i) { return stack[i.offset].front; }
	@safe auto pop(R i) { return stack[i.offset].pop(); }

	@trusted void put(P, R)(R i, Result!(R, P) ans, ulong index = 0) {
		enum id = staticIndexOf!(P, Parsers);
		enum recursive = pgs.leftRecursive[id];
		static assert(id != -1);
		if (i.offset >= m.length)
			alloc.expandArray(m, m.length);
		if (m[i.offset][id] is null)
			m[i.offset][id] = alloc.make!(ETypes[id])(ans, index);
		else
			*m[i.offset][id] = ETypes[id](ans, index);
	}

	@safe void update_lowlink(P)(R i, ulong lowlink) {
		enum id = staticIndexOf!(P, Parsers);
		static assert(id != -1);
		static if (!pgs.leftRecursive[id]) {
			return;
		} else {
			assert(m[i.offset][id] !is null);
			if (m[i.offset][id].lowlink > lowlink)
				m[i.offset][id].lowlink = lowlink;
		}
	}
	@safe void clear_index_lowlink(P)(R i) {
		enum id = staticIndexOf!(P, Parsers);
		static assert(id != -1);
		m[i.offset][id].lowlink = 0;
		m[i.offset][id].index = 0;
	}

	@safe void clear_tenative(P)(R i) {
		enum id = staticIndexOf!(P, Parsers);
		static assert(id != -1);
		m[i.offset][id].tentative = false;
	}

	@safe void clear_tenative(R i, uint id) {
		final switch(id) {
		foreach(j, P; Parsers) {
			static if (pgs.leftRecursive[j]) {
			case j:
				m[i.offset][j].tentative = false;
				return;
			}
		}
		}
	}

	@safe void clear_index_lowlink(R i, uint id) {
		final switch(id) {
		foreach(j, P; Parsers) {
			static if (pgs.leftRecursive[j]) {
			case j:
				m[i.offset][j].lowlink = 0;
				m[i.offset][j].index = 0;
				return;
			}
		}
		}
	}

	@safe void update_current_lowlink(R i, ulong lowlink) {
		final switch(parser_id) {
		foreach(j, P; Parsers) {
			static if (pgs.leftRecursive[j]) {
			case j:
				return update_lowlink!(Parsers[j])(i, lowlink);
			}
		}
		}
	}

	@safe this(Alloc alloc, size_t reserve = 1000) {
		this.alloc = alloc;
		if (reserve == 0)
			reserve = 1;
		m = alloc.makeArray!(typeof(m[0]))(reserve);
		stack = alloc.makeArray!Stack(reserve);
	}
	@trusted ~this() {
		foreach(ref mm; m)
		foreach(ref e; mm)
			if (e !is null) alloc.dispose(e);
		alloc.dispose(m);
	}
}

unittest {
	import std.experimental.allocator.gc_allocator : GCAllocator;
	int[] a;
	auto b = a.withOffset;
	auto m = Memo!(typeof(b), shared(GCAllocator), PGS([false], [false]), int)(GCAllocator.instance);

	m.put(b, makeResult(b, 10));

	auto g = m.get!int(b);
	assert(g.ans.result == 10);
}

struct Location {
	ulong line, col;
}

struct ParserError {
	Location loc;
	string msg;
}

/+ Used for holding an parse error, while still allow parsing to
   continue. `p` is used for error recovery.
 +/
struct Error(alias p) {
	ParserError err;
}

struct Result(R, T = VoidT, Alloc = void)
if (isRangeAcceptable!R && !is(R == ParserError)) {
	private struct RNR {
		R r;
		T result;
	}
	private union {
		RNR ok;
		ParserError _err;
	}
	bool is_ok;
	this(ParserError e) {
		err = e;
		is_ok = false;
	}
	static if (!is(Alloc == void)) {
		Alloc alloc;
		~this() {
			if (is_ok)
				alloc.dispose(ok.result);
		}
		this(R i, Alloc a, T t = T.init) {
			alloc = a;
			ok = RNR(i, t);
			is_ok = true;
		}
	} else {
		this(R i, T t = T.init) {
			ok = RNR(i, t);
			is_ok = true;
		}
	}
	@property ref inout(T) result() inout {
		enforce(is_ok, "Trying to get a result from an error");
		return ok.result;
	}
	@property ref inout(R) next() inout {
		enforce(is_ok, "Trying to get a range from an error");
		return ok.r;
	}
	@property long next_offset() const {
		if (!is_ok) return -1;
		return ok.r.offset;
	}
	@property ref inout(ParserError) err() inout {
		enforce(!is_ok, "Trying to get an error from a ok result");
		return _err;
	}
}

auto makeResult(R, T)(R i, T t) {
	return Result!(R, T)(i, t);
}

struct Span(R) if (isForwardRange!R) {
	R r;
	Location begin, end;
}

enum isRangeAcceptable(R) = isForwardRange!R && hasSlicing!R && !isInfinite!R && hasOffset!R;

package struct Quote(T...) { alias quoted = T; alias quoted this; }

/// Is A a derived class of B?
package template isDerived(B...) if (B.length == 1) {
	static if (is(B[0] == class) || is(B[0] == interface)) {
		template isDerived(A...) {
			static if (A.length != 1)
				enum isDerived = false;
			static if ((is(A[0] == class) || is(A[0] == interface)))
				enum isDerived = staticIndexOf!(B[0], BaseTypeTuple!(A[0])) != -1;
			else
				enum isDerived = false;
		}
	} else
		enum isDerived(A...) = false;
}

// Parser structs
@internal
package struct _Token(string tok) if (tok.length > 0) { }
alias Token(string tok) = _Token!tok[0];

@internal
package struct _Epislon { }
alias Epislon = _Epislon[0];

@internal
struct Optional(T) if (!is(T == Optional!S, S)) {
	Nullable!T v;
	alias v this;
}

@internal
struct Optional(T: S[0], S) {
	bool isNull;
}

@internal
struct Optional(T: S[], S) {
	S[] v;
	bool isNull() { return v.length == 0; }
	alias v this;
}

// Attributes
struct internal { }
struct variants(T...) { alias inner = T; }
struct localVariants { }
struct variantsOnly { }
struct surround(L_, R_, bool optional_) {
	alias L = L_;
	alias R = R_;
	enum optional = optional_;
}

// Ranges

enum hasOffset(R) = is(typeof(R.init.offset) : size_t);

struct offsetRange(R) if (isForwardRange!R) {
	size_t offset;
	R inner;
	this(R i, size_t o = 0) { inner = i; offset = o; }

	static if (hasLength!R) {
		@property auto length() { return inner.length; }
		size_t opDollar(size_t dim: 0)() { return inner.length; }
	}

	@property bool empty() { return inner.empty; }
	@property auto ref front() { return inner.front; }
	void popFront() { offset++; return inner.popFront; }
	auto save() { return typeof(this)(inner, offset); }

	static if (hasSlicing!R) {
		size_t[2] opSlice(size_t dim: 0)(size_t start, size_t end) {
			return [start, end];
		}
		auto opIndex(size_t[2] i) {
			return typeof(this)(inner[i[0]..i[1]], offset+i[0]);
		}
	}
}

template DedupPrepend(T, Set...) {
	static if (staticIndexOf!(T, Set) != -1)
		alias DedupPrepend = AliasSeq!Set;
	else
		alias DedupPrepend = AliasSeq!(T, Set);
}

// Merge two list of unique elements.
// (Actually only Q is assumed to be unique)
template DedupMerge(Q, T...) {
	static if (T.length == 0)
		alias DedupMerge = Q.tuple;
	else
		alias DedupMerge = DedupMerge!(Quote!(DedupPrepend!(T[0], Q.tuple)), T[1..$]);
}

template DedupSeq(T...) {
	alias DedupSeq = DedupMerge!(Quote!(), T);
}

auto withOffset(R)(R i) { return offsetRange!R(i); }

unittest {
	static assert(isRangeAcceptable!(offsetRange!(int[])));
}
