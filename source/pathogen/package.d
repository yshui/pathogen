module pathogen;
import std.experimental.allocator;
import std.experimental.allocator.gc_allocator : GCAllocator;
import std.range;
import std.exception;

alias Void = void[0];

private struct _VoidError { }
alias VoidError = _VoidError[0];

private struct _VoidT { }
alias VoidT = _VoidT[0];

struct Result(R, T = VoidT, E = VoidError) if (isRangeAcceptable!R) {
	private struct RNR {
		R r;
		T result;
	}
	private union {
		RNR ok;
		E _err;
	}
	bool is_ok;
	this(R i, T t) {
		ok = RNR(i, t);
		is_ok = true;
	}
	this(E e) {
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
	@property ref inout(E) err() inout {
		enforce(!is_ok, "Trying to get an error from a ok result");
		return _err;
	}
}

struct Span(R) if (isForwardRange!R) {
	R r;
	uint start_line, start_col;
	uint end_line, end_col;
}

private struct _Token(string tok) { }
alias Token(string tok) = _Token!tok[0];

enum isRangeAcceptable(R) = isForwardRange!R && hasSlicing!R && !isInfinite!R;

unittest {
	static assert(isRangeAcceptable!(dchar[]));
}

template genParser(T: _Token!tok[0], string tok) {
	// Parse a 'tok' from the front of range 'i'.
	// Result is discarded, because the only meaningful info
	// is whether the 'tok' matches
	Result!R genParser(R, Alloc)(R i, Alloc alloc = GCAllocator.instance) {
		return Result!R(VoidError.init);
	}
}

template genParser(T) if (is(T == enum)) {
	// Parse a enum. enum members are seen as different choices.
	// Each member is parsed as specified in their UDA
	Result!(R, T) genParser(R, Alloc)(R i, Alloc alloc = GCAllocator.instance) {

	}
}

unittest {
	auto r1 = genParser!(Token!"asdf")("asdf"d);
}
