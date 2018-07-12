module pathogen.gene;
import pathogen.base;

template gene() {

import std.experimental.allocator;
import std.experimental.allocator.gc_allocator : GCAllocator;
import std.range;
import std.traits;
import std.exception;
import std.meta;
import std.variant;

@safe:
private struct genRuleCon(T, Parsers...) {
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
	static if (Attrs.length == 0)
		mixin genRuleImpl!(T, Parsers);
	else {
		private struct Inner {
			mixin genRuleImpl!(T, Parsers);
		}
		static if (is(typeof(Inner.ruleName)))
			enum ruleName = Inner.ruleName;

		private alias s = Filter!(hasType!surround, Attrs);
		static assert(s.length <= 1, "Can't have multiple surround attributes.");
		static if (s.length == 1) {
			alias innerRules = AliasSeq!(Inner.innerRules, s[0].L, s[0].R);
			private enum desc1 = "( "~getDesc!(s[0].L)~" ) ( "~Inner.desc~" ) ( "~getDesc!(s[0].R)~" )";
			static if (s[0].optional)
				enum desc = "( " ~ desc1 ~ " ) | " ~ Inner.desc;
			else
				enum desc = desc1;
			static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
				alias lp = pathogen!(s[0].L, Parsers);
				auto lr = lp!(R, Alloc)(i, m, alloc);
				if (!lr.is_ok && !s[0].optional)
					return Result!(R, T)(lr.err);

				alias mp = pathogen!(T, Parsers);
				auto mr = mp!(R, Alloc)(lr.is_ok ? lr.next : i, m, alloc);
				if (!mr.is_ok)
					return mr;

				alias rp = pathogen!(s[0].R, Parsers);
				auto rr = rp!(R, Alloc)(mr.next, m, alloc);
				if (rr.is_ok != lr.is_ok)
					return Result!(R, T)(lr.is_ok ? rr.err : lr.err);
				return mr;
			}
		} else {
			alias innerRules = Inner.innerRules;
			enum desc = Inner.desc;
			alias parse = Inner.parse;
		}
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
		static if (is(typeof(rc.ruleName) == string)) {
			parts ~= rc.ruleName;
		} else
			parts ~= "( "~getDesc!u~" )";
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

template genRuleImpl(T: Epislon[0], _...) {
	enum desc = "ε";
	alias innerRules = AliasSeq!();
	static Result!R parse(R, Alloc)(R i, Alloc alloc) {
		return Result!R(i);
	}
}

template genRuleImpl(T, Parsers...) if (is(T == Optional!S, S)) {
	static if (is(T == Optional!S, S))
		alias I = S;
	enum desc = "( " ~ getDesc!I ~ " )?";
	alias innerRules = AliasSeq!I;
	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		alias p = pathogen!(S, Parsers);
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
			ret = r.result;
			return Result!(R, T)(next, ret);
		}
	}
}

template getDesc(T) {
	private enum getDesc = genRuleCon!T.desc;
}

template getNamedDesc(T) {
	private alias t = genRuleCon!T;
	private enum getNamedDesc = t.ruleName~" ::= "~t.desc;
}

template genRuleImpl(T, Parsers...)
if (is(T == _Token!tok[0], string tok)) {
static if (is(T == _Token!tok[0], string tok)) {
	alias innerRules = AliasSeq!();
	enum desc = "\""~tok~"\"";
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
}

template genRuleImpl(T, Parsers...)
if (is(T == enum) && __traits(getAttributes, T).length != 0) {
	private alias attr = AliasSeq!(__traits(getAttributes, T));
	enum ruleName = T.stringof;
	alias innerRules = AliasSeq!(attr);
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
		return Result!(R, T)(VoidError.init);
	}
}

version(none) {
template pathogen(T: VariantN!(max, U), size_t max, U...) {
	Result!(R, T) pathogen(R, Alloc)(R i, Alloc alloc) {

	}
}

template genRuleImpl(T: VariantN!(max, U), size_t max, U...) {
	alias innerRules = U;
	enum desc = orRulesDesc!U;
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
	enum desc = seqRulesDesc!(Fields!T)~(v.length ? " | "~orRulesDesc!(getClassVariants!T) : "");
	enum ruleName = T.stringof;

	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
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
	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		return Result!(R, T)(i, T.init);
	}
}

template genRuleImpl(T, Parsers...) if (is(T == S*, S) && !is(S == class)) {
	static if (is(T == S_*, S_))
		alias S = S_;
	private alias rc = genRuleCon!S;
	alias innerRules = AliasSeq!(S, rc.innerRules);
	enum desc = rc.desc;
	enum ruleName = rc.ruleName~"_ptr";
	static Result!(R, T) parse(R, Alloc)(R i, ref Memo!(R, Alloc, Parsers) m, auto ref Alloc alloc) {
		alias p = pathogen!(S, Parsers);
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

template dumpRules(T...) {
	private static string impl() {
		return [ staticMap!(getNamedDesc, T) ].join("\n");
	}
	enum dumpRules = impl;
}

template dumpCompleteRule(T) {
	enum dumpCompleteRule = dumpRules!(Filter!(hasName, ruleClosure!T));
}

template pathogen(T, Parsers...) {
	static if (Parsers.length == 0)
		private alias allRules = ruleClosure!T;
	else
		private alias allRules = Parsers;
	auto pathogen(R, Alloc)(R i, ref Memo!(R, Alloc, allRules) m, auto ref Alloc alloc) {
		auto r = m.get!T(i);
		if (r !is null)
			return r.ans;
		auto r2 = genRuleCon!(T, allRules).parse!(R, Alloc)(i, m, alloc);
		m.put(i, r2);
		return r2;
	}

	auto pathogen(R, Alloc)(R i, auto ref Alloc alloc) {
		static if (isRangeAcceptable!R) {
			auto m = Memo!(R, Alloc, allRules)(alloc);
			auto j = i;
		} else {
			static assert(isRangeAcceptable!(offsetRange!R));
			auto m = Memo!(offsetRange!R, Alloc, allRules)(alloc);
			auto j = i.withOffset;
		}
		return pathogen!(typeof(j), Alloc)(j, m, alloc);
	}
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
	pragma(msg, dumpCompleteRule!s1);
	auto r3 = pathogen!(s1*)(""d, GCAllocator.instance);
	writeln(*r3.result);

	struct s2 {
		Token!"1" a;
		s1 op;
		Token!"2" b;
	}
	pragma(msg, dumpCompleteRule!s2);

	@surround!(Token!"(", Token!")", true)
	struct s3 {
		Token!"asdf" x;
	}
	pragma(msg, dumpCompleteRule!s3);

	//auto r2 = genParser!Op("+"d);
	class Z { }
	//pathogen!Z("asdf"d);
	pragma(msg, dumpCompleteRule!C1);

	pragma(msg, getDesc!(Optional!C1));
}
}
