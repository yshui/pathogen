module pathogen.gene;
import pathogen.base;

package template gene() {

import std.experimental.allocator;
import std.experimental.allocator.gc_allocator : GCAllocator;
import std.range;
import std.traits;
import std.exception;
import std.meta;
import std.variant;
import pathogen.utils : scc;
debug import std.stdio;

@safe:
private template genRuleCon(T, Parsers...) {
	static if (__traits(compiles, AliasSeq!(__traits(getAttributes, T))))
		private alias Attrs = AliasSeq!(__traits(getAttributes, T));
	else
		private alias Attrs = AliasSeq!();

	/// Does S have type T
	private template hasType(T...) if (T.length == 1) {
		static if (is(T)) {
			template hasType(S...) if (S.length == 1) {
				enum hasType = is(typeof(S[0]) == T[0]);
			}
		} else static if (__traits(isTemplate, T)) {
			template hasType(S...) if (S.length == 1) {
				enum hasType = isInstanceOf!(T[0], S[0]);
			}
		}
	}

	/// Does T have type S
	private template hasTypeR(T...) if (T.length == 1) {
		template hasTypeR(S...) if (S.length == 1) {
			private alias h = hasType!(S[0]);
			enum hasTypeR = h!(T[0]);
		}
	}

	/// Does S match any type in T...
	private template hasAnyType(T...) {
		template hasAnyType(S...) if (S.length == 1) {
			enum hasAnyType = anySatisfy(hasTypeR!S, T);
		}
	}
	private alias Inner = genRuleImpl!(T, Parsers);
	static if (is(typeof(Inner.ruleName) == string))
		enum ruleName = Inner.ruleName;

	private alias s = Filter!(hasType!surround, Attrs);
	static assert(s.length <= 1, "Can't have multiple surround attributes.");
	static if (s.length == 1) {
		alias innerRules = AliasSeq!(Inner.innerRules, s[0].L, s[0].R);
		static bool calcEmptiness()(ref DFSState!bool state) {
			return .calcEmptiness!(s[0].L, Parsers)(state) &&
			       .calcEmptiness!(T, Parsers)(state) &&
			       .calcEmptiness!(s[0].R, Parsers)(state);
		}
		private alias l = leftMostOfSeq!Parsers;
		alias leftMost = l!(s[0].L, T, s[0].R);
		private enum desc1 = "( "~getDesc!(s[0].L)~" ) ( "~Inner.desc~" ) ( "~getDesc!(s[0].R)~" )";
		static if (s[0].optional)
			enum desc = "( " ~ desc1 ~ " ) | " ~ Inner.desc;
		else
			enum desc = desc1;
		static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
			alias lp = pathogenImpl!(s[0].L, Parsers);
			auto lr = lp!(R, Alloc)(i, m, alloc);
			if (!lr.is_ok && !s[0].optional)
				return Result!(R, T)(lr.err);

			alias mp = pathogenImpl!(T, Parsers);
			auto mr = mp!(R, Alloc)(lr.is_ok ? lr.next : i, m, alloc);
			if (!mr.is_ok)
				return mr;

			alias rp = pathogenImpl!(s[0].R, Parsers);
			auto rr = rp!(R, Alloc)(mr.next, m, alloc);
			if (rr.is_ok != lr.is_ok)
				return Result!(R, T)(lr.is_ok ? rr.err : lr.err);
			return mr;
		}
	} else {
		alias innerRules = Inner.innerRules;
		enum desc = Inner.desc;
		alias parse = Inner.parse;
		alias calcEmptiness = Inner.calcEmptiness;
		alias leftMost = Inner.leftMost;
	}
}

version(unittest) {
	@localVariants
	class C1 {
		Token!"asdf" x;
	}
	class C2: C1 {
		Token!"qwe" y;
	}
	class C3: C1 { }
	class D {  }

	interface I {}
	class D1: I {}
	class D2: I {}
	@localVariants
	class B {
		B a1;
		Token!"z" a2;
		@safe this(B x, Token!"z") { a1 = x; }
		@safe this() {}
	}
	class A {
		B a1;
		@safe this(B x) { a1 = x; }
	}
	class B2: B {
		A a1;
		Token!"j" a2;
		@safe this(A x, Token!"j") { a1 = x; }
	}
	class B3: B {
		A a1;
		Token!"x" a2;
		@safe this(A x, Token!"x") { a1 = x; }
	}
	class B4: B {
		Token!"x" a1;
		@safe this(Token!"x") { }
	}

}

private template getClassVariants(T) {
	static if (hasUDA!(T, variants)) {
		alias getClassVariants = getUDAs!(T, variants)[0].inner;
		static assert (allSatisfy!(isDerived!T, getVariants));
	} else static if (hasUDA!(T, localVariants) || is(T == interface)){
		// interface doesn't have a self rule, so it always wants variants
		alias p = AliasSeq!(__traits(parent, T))[0];
		private template getM(alias T) {
			alias getM(string n) = AliasSeq!(__traits(getMember, T, n))[0];
		}

		alias allM = staticMap!(getM!p, __traits(allMembers, p));
		alias getClassVariants = Filter!(isDerived!T, allM);
	} else
		alias getClassVariants = AliasSeq!();
}

private string seqRulesDesc(T...)() {
	string[] parts;
	static if (T.length == 0)
		parts ~= "ε";
	foreach(u; T) {
		alias rc = genRuleCon!u;
		alias allM = AliasSeq!(__traits(allMembers, rc)); // Hack for issue 19190
		static if (is(typeof(rc.ruleName))) {
			parts ~= rc.ruleName;
		} else {
			parts ~= "( "~getDesc!u~" )";
		}
	}
	return parts.join(" ");
}

private string orRulesDesc(T...)() {
	string[] parts;
	foreach(u; T) {
		alias rc = genRuleCon!u;
		static if (is(typeof(rc.ruleName) == string)) {
			parts ~= rc.ruleName;
		} else
			parts ~= "( "~getDesc!u~" )";
	}
	return parts.join(" | ");
}

// parser template can use this to check if PGS is passed to the template
// and use it accordingly.
private enum hasPGS(T...) = is(typeof(T[0]) == PGS);

template genRuleImpl(T: Epislon, _...) {
	enum desc = "ε";
	alias innerRules = AliasSeq!();
	alias leftMost = AliasSeq!();
	static bool calcEmptiness(in ref DFSState!bool) {
		return true;
	}
	static Result!(R, T) parse(R, Alloc)(R i, Alloc alloc) {
		return Result!(R, T)(i, Epislon.init);
	}
}

template genRuleImpl(T, Parsers...) if (is(T == Optional!S, S)) {
	static if (is(T == Optional!S, S))
		alias I = S;
	alias leftMost = AliasSeq!S;
	enum desc = "( " ~ getDesc!I ~ " )?";
	alias innerRules = AliasSeq!I;
	static bool calcEmptiness(in ref DFSState!bool) {
		return true;
	}
	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		alias p = pathogenImpl!(S, Parsers);
		auto r = p!(R, Alloc)(i, m, alloc);
		T ret;
		R next = r.is_ok ? r.next : i;
		static if (is(S: O[0], O)) {
			ret = T(r.is_ok);
			return Result!(R, T)(next, ret);
		} else static if (is(S: O[], O)) {
			if (r.is_ok)
				ret.v = r.result;
			return Result!(R, T)(next, ret);
		} else {
			if (r.is_ok)
				ret = r.result;
			return Result!(R, T)(next, ret);
		}
	}
}

template getDesc(T) {
	alias rc = genRuleCon!T;
	private enum getDesc = rc.desc;
}

template getNamedDesc(T) {
	private alias t = genRuleCon!T;
	private enum getNamedDesc = t.ruleName~" ::= "~t.desc;
}

private template getLeftMost(PGS pgs, Parsers...) {
	alias getLeftMost(T) = genRuleCon!(T, pgs, Parsers).leftMost;
}

template genRuleImpl(T, Parsers...)
if (is(T == _Token!tok, string tok)) {
	static if (is(T == _Token!_tok, string _tok))
		enum tok = _tok;
	alias innerRules = AliasSeq!();
	alias leftMost = AliasSeq!();
	enum desc = "\""~tok~"\"";
	static bool calcEmptiness()(in ref DFSState!bool) {
		return tok == "";
	}
	// Parse a 'tok' from the front of range 'i'.
	// Result is discarded, because the only meaningful info
	// is whether the 'tok' matches
	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		import std.algorithm.searching;
		if (!i.startsWith(tok))
			return Result!(R, T)(ParserError.init);
		return Result!(R, T)(i[tok.length..$]);
	}
}

template genRuleImpl(T, Parsers...) if (is(T == S[0], S)) {
	static if (is(T == S[0], S))
		alias rc = genRuleCon!(S, Parsers);
	alias leftMost = AliasSeq!S;
	alias innerRules = AliasSeq!(S, rc.innerRules);
	enum desc = rc.desc;
	static bool calcEmptiness()(ref DFSState!bool state) {
		return .calcEmptiness!(S, Parsers)(state);
	}
	static if (is(typeof(rc.ruleName) == string))
		enum ruleName = rc.ruleName ~ "_discarded";
	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		alias p = pathogenImpl!(S, Parsers);
		auto r = p!(R, Alloc)(i, m, alloc);
		if (!r.is_ok)
			return Result!(R, T)(r.err);
		return Result!(R, T)(r.next, []);
	}
}

template genRuleImpl(T, Parsers...)
if (is(T == enum) && __traits(getAttributes, T).length != 0) {
	private alias attr = AliasSeq!(__traits(getAttributes, T));
	enum ruleName = T.stringof;
	alias innerRules = AliasSeq!attr;
	alias leftMost = attr;
	static bool calcEmptiness()(ref DFSState!bool state) {
		bool ret = false;
		foreach(i; attr)
			ret = ret || .calcEmptiness!(i, Parsers)(state);
		return ret;
	}
	private static auto dumpEnum() {
		alias members = EnumMembers!T;
		static assert(members.length == attr.length,
		              "Number of tokens doesn't match the number of enum members");

		import std.array;
		return [ staticMap!(getDesc, attr) ].join(" | ");
	}
	enum desc = dumpEnum;
	// Parse a enum. enum members are seen as different choices.
	// Each member is parsed as specified in their UDA
	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		alias attr = AliasSeq!(__traits(getAttributes, T));
		alias members = EnumMembers!T;

		static assert(members.length == attr.length,
		              "Number of tokens doesn't much the number of enum members");
		foreach(j, a; attr) {
			alias p = pathogenImpl!(a, Parsers);
			auto r = p!(R, Alloc)(i, m, alloc);
			if (r.is_ok)
				return Result!(R, T)(i, members[j]);
		}
		return Result!(R, T)(ParserError.init);
	}
}

template leftMostOfSeq(P...) {
	static if (hasPGS!P) {
		private enum pgs = P[0];
		private alias Parsers = P[1..$];
		template leftMostOfSeqImpl(T...) {
			static if (T.length == 0)
				alias leftMostOfSeqImpl = AliasSeq!();
			else {
				private enum id = staticIndexOf!(T[0], Parsers);
				static if (pgs.matchesEmpty[id])
					alias leftMostOfSeqImpl = DedupPrepend!(T[0], leftMostOfSeqImpl!(T[1..$]));
				else
					alias leftMostOfSeqImpl = AliasSeq!(T[0]);
			}
		}
		alias leftMostOfSeq = leftMostOfSeqImpl;
	} else {
		alias leftMostOfSeq(T...) = AliasSeq!();
	}
}

/+ Generate parser for classes.
 + If the class has a `@localVariants` attributes, all dervied claases defined at the same level
 + are considered a branch in this class' grammar rule. If it has a `@variants!T` attributes, all of
 + T are considered branches.
 +
 + Note: inherited fields are not included in the grammar.
 +/

template genRuleImpl(T, Parsers...) if (is(T == class) && !hasUDA!(T, internal)) {
	// class rules ::= self | all variants
	alias innerRules = AliasSeq!(Fields!T, getClassVariants!T);
	private alias v = getClassVariants!T;
	private alias l = leftMostOfSeq!Parsers;
	alias leftMost = AliasSeq!(l!(Fields!T), v);
	enum desc = seqRulesDesc!(Fields!T)~(v.length ? " | "~orRulesDesc!(getClassVariants!T) : "");
	enum ruleName = T.stringof;
	static bool calcEmptiness()(ref DFSState!bool state) {
		auto ret = true;
		foreach(i; Fields!T)
			ret = ret && .calcEmptiness!(i, Parsers)(state);
		foreach(i; v)
			ret = ret || .calcEmptiness!(i, Parsers)(state);
		return ret;
	}

	@trusted static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		bool parsed = true;
		R next = i;
		Fields!T f;
		foreach(fi, F; Fields!T) {
			alias p = pathogenImpl!(F, Parsers);
			auto r = p!(R, Alloc)(next, m, alloc);
			if (!r.is_ok) {
				parsed = false;
				break;
			}
			f[fi] = r.result;
			next = r.next;
		}
		if (parsed)
			return Result!(R, T)(next, alloc.make!T(f));

		foreach(v; getClassVariants!T) {
			alias p = pathogenImpl!(v, Parsers);
			auto r = p!(R, Alloc)(i, m, alloc);
			if (r.is_ok)
				return Result!(R, T)(r.next, cast(T)r.result);
		}

		return Result!(R, T)(ParserError.init);
	}
}

unittest {
	static assert(is(getClassVariants!C1 == AliasSeq!(C2, C3)));
	static assert(is(getClassVariants!I == AliasSeq!(D1, D2)));
}

template genRuleImpl(T, Parsers...) if (is(T == struct) && !hasUDA!(T, internal)) {
	alias innerRules = Fields!T;
	enum ruleName = T.stringof;
	enum desc = seqRulesDesc!innerRules;
	private alias l = leftMostOfSeq!Parsers;
	alias leftMost = l!(Fields!T);
	static bool calcEmptiness()(ref DFSState!bool state) {
		auto ret = true;
		foreach(i; innerRules)
			ret = ret && .calcEmptiness!(i, Parsers)(state);
		return ret;
	}
	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		bool parsed = true;
		R next = i;
		Fields!T f;
		foreach(fi, F; Fields!T) {
			alias p = pathogenImpl!(F, Parsers);
			auto r = p!(R, Alloc)(next, m, alloc);
			if (!r.is_ok) {
				parsed = false;
				debug writeln(F.stringof~" parse failed");
				break;
			}
			debug(StructParser) writeln(F.stringof~" parse succeeded");
			f[fi] = r.result;
			next = r.next;
		}
		if (parsed)
			return Result!(R, T)(next, T(f));
		return Result!(R, T)(ParserError.init);
	}
}

template genRuleImpl(T, Parsers...) if (is(T == S*, S) && !is(S == class) && !is(T == Optional!V, V)) {
	static if (is(T == S_*, S_))
		alias S = S_;
	private alias rc = genRuleCon!(S, Parsers);
	private alias allM = AliasSeq!(__traits(allMembers, rc)); // Hack for issue 19190
	alias innerRules = S;
	enum desc = rc.ruleName;
	enum ruleName = rc.ruleName~"_ptr";
	alias leftMost = AliasSeq!S;
	static bool calcEmptiness()(ref DFSState!bool state) {
		return .calcEmptiness!(S, Parsers)(state);
	}
	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		alias p = pathogenImpl!(S, Parsers);
		auto r = p!(R, Alloc)(i, m, alloc);
		if (!r.is_ok)
			return Result!(R, T)(r.err);

		import std.algorithm.mutation : swap;
		T ret = alloc.make!S;
		swap(*ret, r.result);
		return Result!(R, T)(r.next, ret);
	}
}

/+ Generate a closure of the given rules.
 + The given rules will always be at the front of the returned list
 +/
private template ruleClosure(T...) {
	private template ruleClosureImpl(Q, T...) if (isInstanceOf!(Quote, Q)) {
		private alias S = Q.quoted;
		static if (T.length == 0)
			alias ruleClosureImpl = S;
		else static if (staticIndexOf!(T[0], S) != -1)
			alias ruleClosureImpl = ruleClosureImpl!(Q, T[1..$]);
		else {
			private alias rc = genRuleCon!(T[0]);
			alias ruleClosureImpl = ruleClosureImpl!(Quote!(S, T[0]), T[1..$], rc.innerRules);
		}
	}
	alias ruleClosure = ruleClosureImpl!(Quote!(), T);
}

private enum hasName(T) = is(typeof(genRuleCon!T.ruleName) == string);

struct DFSState(T) {
	T[] result;
	bool[int] visited;
	this(int size) {
		result = new T[size];
	}
}

private bool calcEmptiness(Now, Parsers...)(ref DFSState!bool state) {
	assert(__ctfe);
	auto id = staticIndexOf!(Now, Parsers);
	assert(id >= 0);
	if (id in state.visited)
		return state.result[id];
	state.result[id] = false;
	state.visited[id] = true;
	alias rc = genRuleCon!(Now, Parsers);
	state.result[id] = rc.calcEmptiness(state);
	return state.result[id];
}

private auto calcEmptiness(Parsers...)() {
	assert(__ctfe);
	auto state = DFSState!bool(Parsers.length);
	foreach(i; Parsers)
		calcEmptiness!(i, Parsers)(state);
	return state.result;
}

private template getAdjacent(P, PGS pgs, Parsers...) {
	private alias l = getLeftMost!(pgs, Parsers);
	enum getAdjacent = [staticMap!(ApplyRight!(staticIndexOf, Parsers), l!P)];
}

private bool[] calcLeftRecursiveness(PGS pgs, Parsers...)() {
	enum g = [staticMap!(ApplyRight!(getAdjacent, pgs, Parsers), Parsers)];
	enum scc = g.scc;
	alias l = getLeftMost!(pgs, Parsers);
	uint[] mcnt = new uint[Parsers.length+1];
	foreach(i; scc)
		mcnt[i]++;
	bool[] ret = new bool[Parsers.length];
	foreach(i, P; Parsers)
		ret[i] = (mcnt[scc[i]] != 1) || (staticIndexOf!(P, l!P) != -1);
	return ret;
}

template pathogenImpl(T, PGS pgs, Parsers...) {
	static assert(Parsers.length > 0);
	private enum pid = staticIndexOf!(T, Parsers);
	auto nonlrImpl(R, Alloc)(R i, ref Memo!(R, Alloc, pgs, Parsers) m, auto ref Alloc alloc) {
		auto r = m.get!T(i);
		if (r !is null)
			return r.ans;
		size_t prev_offset = m.update_offset(i);
		auto r2 = genRuleCon!(T, pgs, Parsers).parse!(R, Alloc)(i, m, alloc);
		m.put(i, r2);
		m.update_offset(prev_offset);
		return r2;

	}
	auto lrImpl(R, Alloc)(R i, ref Memo!(R, Alloc, pgs, Parsers) m, auto ref Alloc alloc) {
		debug(LR) {
			import std.stdio;
			writeln("Parsing left recursive "~T.stringof);
		}
		auto mr = m.get!T(i);
		debug(LR) writeln(m.m[i.offset]);
		if (mr !is null) {
			if (i.offset != m.offset) {
				assert(!mr.tentative);
				debug(LR) writeln("Move on to next offset");
				return mr.ans;
			}
			if (!mr.tentative) {
				debug(LR) writeln("Result not tentative");
				return mr.ans;
			}
			if (mr.index != 0) {
				debug(LR) writeln("Use tentative result");
				// this parser has been called in this round
				// just update lowlink
				m.update_current_lowlink(i, mr.index);
				return mr.ans;
			}
			// first time this parser is call in current round
			// retry parsing
			debug(LR) writeln("Retry parsing");
		} else
			debug(LR) writeln("No record found");

		size_t prev_offset = m.update_offset(i);
		uint prev_parser = m.update_parser!T;

		if (mr is null) {
			// add a tentative entry
			debug(LR) writeln("Create new record");
			auto r = Result!(R, T)(ParserError.init);
			m.put(i, r, m.index++);
			mr = m.get!T(i);
		} else {
			debug(LR) writeln("Update old record");
			mr.index = m.index++;
			mr.lowlink = mr.index;
		}

		// push parser T onto stack
		m.push!T(i);
		alias parse = genRuleCon!(T, pgs, Parsers).parse;
		auto r = parse!(R, Alloc)(i, m, alloc);
		if (r.next_offset > mr.ans.next_offset)
			mr.ans = r;
		bool progress = true;
		while (mr.lowlink == mr.index && progress) {
			debug(LR) writeln(T.stringof~" is SCC head");
			if (r.is_ok) {
				debug(LR) writeln("Current progress: ", i, "->", r.next);
			}
			// 1. get involved set by poping from stack
			uint[Parsers.length] involved = void;
			long[Parsers.length] next_offset = void;
			long this_next_offset = r.next_offset;
			uint ninvolved;
			while (m.front(i) != pid)
				involved[ninvolved++] = m.pop(i);
			// 2. reset their index and lowlink
			foreach(id; involved[0..ninvolved]) {
				m.clear_index_lowlink(i, id);
				next_offset[id] = m.get_next_offset(i, id);
			}
			// 3. retry parsing T
			r = parse!(R, Alloc)(i, m, alloc);
			// 4. check if any of involved parser made progress
			progress = r.next_offset > this_next_offset;
			if (!progress) {
				foreach(id; involved[0..ninvolved]) {
					if (next_offset[id] > m.get_next_offset(i, id)) {
						progress = true;
						debug(LR) writeln(Parsers.stringof,"[", id, "] made progress");
						break;
					}
				}
			} else {
				debug(LR) writeln("Self made progress");
				mr.ans = r;
			}
			// 5. go to step 7 if no progress is made
			debug(LR) if (progress)
				// 6. go to loop condition
				writeln("Made progress");
		}
		debug(LR) writeln("Finishing up round of parsing, "~T.stringof);
		if (mr.lowlink == mr.index) {
			// If we still are the head of SCC
			// 7. clear tentative flag in all involved parser results
			//    including myself, break
			debug(LR) writeln("Mark as not tenative");
			while (m.front(i) != pid)
				m.clear_tenative(i, m.pop(i));
			m.clear_tenative!T(i);
			m.pop(i);
		} else {
			// Otherwise, we are no longer head of SCC after this round
			// We cannot mark anything not tentative
			debug(LR) writeln("No longer head of SCC");
		}
		m.update_parser(prev_parser);
		if (prev_offset == m.offset)
			m.update_current_lowlink(i, mr.lowlink);
		else
			m.update_offset(prev_offset);
		return mr.ans;
	}

	Result!(R, T) pathogenImpl(R, Alloc)(R i, ref Memo!(R, Alloc, pgs, Parsers) m, auto ref Alloc alloc) {
		static if (pgs.leftRecursive[pid])
			return lrImpl!(typeof(i), Alloc)(i, m, alloc);
		else
			return nonlrImpl!(typeof(i), Alloc)(i, m, alloc);
	}

	auto pathogenImpl(R, Alloc)(R i, auto ref Alloc alloc) {
		static if (isRangeAcceptable!R) {
			auto m = Memo!(R, Alloc, Parsers)(alloc);
			auto j = i;
		} else {
			static assert(isRangeAcceptable!(offsetRange!R));
			auto m = Memo!(offsetRange!R, Alloc, pgs, Parsers)(alloc);
			auto j = i.withOffset;
		}
		static if (pgs.leftRecursive[pid])
			auto r = lrImpl!(typeof(j), Alloc)(j, m, alloc);
		else
			auto r = nonlrImpl!(typeof(j), Alloc)(j, m, alloc);
		foreach(ss; m.stack)
			assert(ss.top == 0);
		return r;
	}
}

template pathogen(T) {
	private alias allRules = ruleClosure!T;
	private enum emptiness = calcEmptiness!allRules();
	private enum pgs = PGS(emptiness,
	    calcLeftRecursiveness!(PGS(emptiness, []), allRules)());
	mixin pathogenImpl!(T, pgs, allRules);
	alias pathogen = pathogenImpl;
}

template dumpRules(T...) {
	private static string impl() {
		return [ staticMap!(getNamedDesc, T) ].join("\n");
	}
	enum dumpRules = impl;
}

template dumpCompleteRule(T) {
	enum dumpCompleteRule = dumpRules!(Filter!(hasName, ruleClosure!T));
}

private template debugInternal(T) {
	private alias allRules = ruleClosure!T;
	private enum pgs = PGS(calcEmptiness!allRules());
	private alias rc = genRuleCon!(T, pgs, allRules);
	alias leftMost = rc.leftMost;
}

unittest {
	import std.experimental.allocator.gc_allocator : GCAllocator;
	// workaround issue 19081
	struct E {
		@(Token!"+", Token!"-")
		enum Op {
			Add,
			Sub,
		}
	}

	alias T1 = Token!"asdf";
	auto r1 = pathogen!T1("asdf"d, GCAllocator.instance);
	import std.stdio;
	assert(r1.is_ok);
	auto r1f = pathogen!T1("asdd"d, GCAllocator.instance);
	assert(!r1f.is_ok);

	auto r2 = pathogen!(Optional!T1)("asdf"d, GCAllocator.instance);
	assert(r2.is_ok);
	writeln(r2.result);
	auto r2f = pathogen!(Optional!T1)("asdd"d, GCAllocator.instance);
	assert(r2f.is_ok);
	writeln(r2f.result);

	struct s1 {
		E.Op o1;
		E.Op o2;
	}
	pragma(msg, dumpCompleteRule!(s1*));
	auto r3 = pathogen!(s1*)(""d, GCAllocator.instance);
	writeln(r3.is_ok);

	struct lr1 {
		Optional!(lr1*) a;
		Token!"+1" b;
	}
	auto tmp = pathogen!lr1("+1+1+1"d, GCAllocator.instance);
	assert(tmp.is_ok);
	writeln(tmp);

	struct s2 {
		Token!"1" a;
		s1 op;
		Token!"2" b;
	}

	pragma(msg, dumpCompleteRule!s2);

	struct s3 {
		Optional!(Token!"asdf") x;
		Token!"qwer" y;
	}
	static assert(is(debugInternal!s3.leftMost == AliasSeq!(Optional!(Token!"asdf"), Token!"qwer")));

	@surround!(Token!"(", Token!")", true)
	struct s4 {
		Token!"asdf" x;
	}
	pragma(msg, dumpCompleteRule!s4);

	//auto r2 = genParser!Op("+"d);
	class Z { }
	//pathogen!Z("asdf"d);
	pragma(msg, dumpCompleteRule!C1);

	pragma(msg, getDesc!(Optional!C1));

	auto r = pathogen!A("xxxzj"d, GCAllocator.instance);
	pragma(msg, dumpCompleteRule!A);
	writeln(r.is_ok);
}
}
