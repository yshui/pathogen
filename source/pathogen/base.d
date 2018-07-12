module pathogen.base;
import std.range;
import std.meta;
import std.traits;
import std.exception;
import std.typecons : Nullable;
import std.experimental.allocator;

alias Void = void[0];

package struct _VoidError { }
alias VoidError = _VoidError[0];

package struct _VoidT { }
alias VoidT = _VoidT[0];

interface IMemoEntry(R) { }
final class MemoEntry(T, R) : IMemoEntry!R {
	Result!(R, T) ans;
	this(Result!(R, T) a) { ans = a; }
}

struct Memo(R, Alloc, Parsers...) if (isRangeAcceptable!R){
	IMemoEntry!R[Parsers.length][] m;
	Alloc alloc;

	@safe auto get(P)(R i) {
		enum id = staticIndexOf!(P, Parsers);
		static assert(id != -1);

		if (m[i.offset][id] is null)
			return null;
		auto ret = cast(MemoEntry!(P, R))m[i.offset][id];
		assert(ret !is null);
		return ret;
	}

	@trusted void put(P, R)(R i, Result!(R, P) ans) {
		enum id = staticIndexOf!(P, Parsers);
		static assert(id != -1);
		if (i.offset >= m.length)
			alloc.expandArray(m, m.length);
		m[i.offset][id] = alloc.make!(MemoEntry!(P, R))(ans);
	}

	@safe this(Alloc alloc, size_t reserve = 1000) {
		this.alloc = alloc;
		m = alloc.makeArray!(typeof(m[0]))(reserve);
	}
}

unittest {
	import std.experimental.allocator.gc_allocator : GCAllocator;
	int[] a;
	auto b = a.withOffset;
	auto m = Memo!(typeof(b), shared(GCAllocator), int)(GCAllocator.instance);

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

struct Result(R, T = VoidT) if (isRangeAcceptable!R && !is(R == ParserError)) {
	private struct RNR {
		R r;
		T result;
	}
	private union {
		RNR ok;
		ParserError _err;
	}
	bool is_ok;
	this(R i, T t = T.init) {
		ok = RNR(i, t);
		is_ok = true;
	}
	this(ParserError e) {
		err = e;
		is_ok = false;
	}
	@property ref inout(T) result() inout {
		enforce(is_ok, "Trying to get a result from an error");
		return ok.result;
	}
	@property ref inout(R) next() inout {
		enforce(is_ok, "Trying to get a range from an error");
		return ok.r;
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
package struct _Token(string tok) if (tok.length > 0) { }
alias Token(string tok) = _Token!tok[0];

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

auto withOffset(R)(R i) { return offsetRange!R(i); }

unittest {
	static assert(isRangeAcceptable!(offsetRange!(int[])));
}
