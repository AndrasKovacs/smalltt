
# smalltt

Demo project for several techniques for high-performance elaboration
with dependent types.

It is a complete rewrite of the [old smalltt
version](https://github.com/AndrasKovacs/smalltt/tree/old-master) which I wrote
mostly in 2018-2019.

## Table of Contents

* [Overview](#overview)
* [Installation](#installation)
* [Language overview](#language-overview)
* [Design](#design)
  * [Basics](#basics)
    * [NbE vs. naive evaluation](#nbe-vs-naive-evaluation)
  * [Contextual metavariables](#contextual-metavariables)
  * [Glued evaluation](#glued-evaluation)
    * [On hash consing](#on-hash-consing)
  * [Approximate conversion checking](#approximate-conversion-checking)
  * [Paired values](#paired-values)
  * [Eta-short meta solutions](#eta-short-meta-solutions)
  * [Meta solution checking and quotation](#meta-solution-checking-and-quotation)
  * [Meta freezing and approximate occurs checking](#meta-freezing-and-approximate-occurs-checking)
* [GHC-specific optimizations](#ghc-specific-optimizations)
  * [IO unboxing](#io-unboxing)
  * [Custom exceptions](#custom-exceptions)
  * [Join-point friendly IO combinators](#join-point-friendly-io-combinators)
  * [Data structures and libraries](#data-structures-and-libraries)
* [Benchmarks](#benchmarks)
  * [Elaboration speed](elaboration-speed)
  * [Elaboration asymptotics](elaboration-asymptotics)
  * [Raw conversion checking](raw-conversion-checking)
  * [Raw evaluation and normalization](raw-evaluation-and-normalization)


### Overview

This project serves as a demo for several techniques for high-performance
elaboration with dependent types. I also include some benchmarks, which are
intended to be as similar as possible across Agda, Lean, Coq and smalltt.

You may skip to [benchmarks](#benchmarks) if you're interested in that.

Work in progress. Code and documentation alike may be subject to change, cleanup
or extension.

### Installation

First, clone or download this repository.

Using `stack`:
- Install [stack](https://docs.haskellstack.org/en/stable/README/).
- Run `stack install` in the smalltt directory. If you have LLVM installed, use
   `stack install --flag smalltt:llvm` instead, that gives some performance
   boost.

Using `cabal`:
- Install [cabal](https://www.haskell.org/cabal/)
- Run `cabal v2-update`.
- Run `cabal v2-install` in the smalltt directory. If you have LLVM, use
  `cabal v2-install -fllvm` instead.

Also make sure that the executable is on the PATH. On Linux-es, the `stack`
install directory is `$HOME/.local/bin`, and the `cabal` one is
`$HOME/.cabal/bin`.

### Language overview

smalltt is a minimal dependent type theory implementation. Features:

- Type-in-type.
- Dependent functions.
- Agda-style implicit functions.
- Basic pattern unification.
- A distinguished top-level scope and local let-definitions.
- An executable which can load a single file at once, and lets us
  query top-level definitions in several ways.

See [Basics.stt](Basics.stt) for introductory examples.


## Design

### Basics

The core design is based on [Coquand's
algorithm](https://www.sciencedirect.com/science/article/pii/0167642395000216). This
is sometimes called "elaboration with normalization-by-evaluation", or "semantic
elaboration". This is becoming the de facto standard design of dependently typed
elaboration nowadays, but it is in fact the preferred design for elaboration
with any type system which includes binders and substitution in types. It is
explained in detail in
- https://davidchristiansen.dk/tutorials/nbe/
- https://github.com/AndrasKovacs/elaboration-zoo

I give a short review. Dependent type checking involves execution of arbitrary
functional programs at compile time. For executing functional programs, the
standard practice (used in virtually all functional languages) is to have

1. Immutable program code, which may be machine code or interpreted code.
2. Runtime objects, consisting of constructors and closures.

The basic idea is to use the above setup during elaboration, with some
extensions.

The elaborator takes as input **raw syntax**, and outputs **core syntax**, which
corresponds to immutable program code. When necessary, we evaluate core syntax
into **semantic values** (or values in short), which correspond to runtime objects,
and indeed they represent function values as closures.

Evaluation and runtime values have to support a somewhat richer feature set than
what is typical in functional languages. They must support **open evaluation**,
that is, evaluation of programs which may contain free variables. This makes it
possible, for instance, to evaluate a function body. In such code, free variables
cause evaluation to **get stuck**, so we there are special values corresponding to
stuck computations; these are called **neutral** values.

Neutral values make it possible to convert runtime values back to core syntax.
This is called **quoting**. Quoting is used in elaboration whenever we need to
serialize or store values. For example, since elaboration outputs core syntax,
whenever we need to fill a hole in raw syntax, we plug the hole by converting a
value to a core term by quoting.

**Normalization by evaluation (NbE)** is normalizing terms by first evaluating
then quoting them. The kind of normal forms that we get can vary depending on
the details of evaluation and quoting. In particular, it is not mandatory that
NbE yields beta-normal terms.

Moreover, values support **conversion checking**. Type equality checking is
required in pretty much any type checker. In dependently typed languages, types
may include arbitrary programs, and equality checking becomes
beta-eta-conversion checking of values. At its simplest, this is implemented by
recursively walking values. The "open" evaluation makes it possible to get
inside closures during conversion checking, so we can check if two functions
have beta-eta-convertible bodies.

#### NbE vs. naive evaluation

Elaboration with NbE can be contrasted to elaboration with "naive"
evaluation. In this style, compile-time evaluation is performed by naive term
substitution, which is far less efficient than NbE. In some implementations,
naive substitution is still used because of its perceived simplicity. However,
my experience is that NbE is significantly simpler to implement, and also easier
to *correctly* implement, than capture-avoiding substitution. Furthermore, any
attempt to use naive substitution in type checking necessitates additional
optimizations, which add more complexity.

For example, Lean uses naive substitution in its kernel, but to recover
acceptable performance it has to add extra machinery (memoization, free variable
annotations on terms for skipping traversals during substitutions). The ends up
being slower and more complicated than an NbE implementation.

In summary, capture-avoiding substitution should be avoided whenever possible in
elaboration implementations. Sometimes it's necessary, but only for niche,
non-performance-critical purposes, in more feature-rich systems. Smalltt uses
no substitution operation whatsoever, and we can go pretty far without one.

(Remark: *cubical type theories* are notorious for requiring substitution from
the get go. It's an open research problem how to get rid of naive substitution
there).

### Contextual metavariables

Smalltt uses **contextual metavariables**. This means that every metavariable
is a function which abstracts over the bound variables in its scope. Take
the following surface code.
```
id : (A : U) → A → A
 = λ A x. x

id2 : (A : U) → A → A
 = λ A x. id _ x
```
When the elaborator hits the hole in `id2`, it fills it with a fresh metavariable
which abstracts over `A` and `x`. The elaboration output is:
```
id : (A : U) → A → A
  = λ A x. x

?0 = λ A x. A

id2 : (A : U) → A → A
  = λ A x. id (?0 A x) x
```
Note that `?0` is a fresh top-level definition and the hole gets plugged with it.
Smalltt's particular flavor of contextual metavariables puts metas in mutual top-level
blocks in the elaboration output. Other setups are possible, including elaborating solved
metas to local let-definitions, but those are significantly more complicated to implement.

Also, smalltt uses basic **pattern unification** for producing meta solutions.
See
[this](https://github.com/AndrasKovacs/elaboration-zoo/blob/master/03-holes/Main.hs)
for a tutorial on the basics of contextual metavariables and pattern
unification.

Smalltt does not try very hard to optimize the representation of contextual
metas, it just reuses plain lambdas to abstract over scopes. See this for a
discussion in Coq: https://github.com/coq/coq/issues/12526. As a result, basic
operations involving metas are usually linear in the size of the local scope.
My benchmarking showed that this is not a significant bottleneck in realistic
user-written code, and we don't really have machine-generated code (e.g. by
tactics) that could introduce pathological cases.

### Glued evaluation

The most basic NbE setup is not adequate for performance. The problem is that
we need different features in conversion checking and in quoting:

- In basic conversion checking, we want to evaluate as efficiently as possible.
- In quoting, we want to output terms which are *as small as possible*. The
  reason is that, through metavariable solutions, the output of quoting is
  included in the overall elaboration output. So, if quoting returns full
  beta-normal terms, that reliably destroys performance, as normal forms are
  tend to be extremely large.

The solution is to add control over **definition unfolding** to evaluation and
quotation. We call the implementation **glued evaluation**, as the evaluator
lazily computes two different values on each unfolding choice. In smalltt we
have unfolding control only for top-level definitions. This simplifies
implementation, and usually top-level scopes are vastly larger than local
scopes, so we already capture the vast majority of size compression by only
focusing on top-level unfolding.

See [this
file](https://github.com/AndrasKovacs/elaboration-zoo/blob/master/GluedEval.hs)
for a minimal demo of glued evaluation. In short, top-level variables are
evaluated to values which represent lazy ("non-deterministic") choice between
unfolding the definition, and not unfolding it. This has a noticeable constant
overhead during evaluation but overall the trade-off is well worth it. Later,
the quotation function has the choice of visiting either evaluation branches, or
both, in which case as much as possible computation is shared between the
branches.

When we need high-performance evaluation during conversion checking, we have it,
and when we solve a metavariable, we are able to quote values to terms which are
*minimal* with respect to top-level unfolding. This is also useful in error
message reporting and interaction, where we want to be able to display small
terms.

Only being able to control top-level unfolding is not quite sufficient for
sophisticated interactive proving, but the technique here could be extended
to richer unfolding control with modest additional overheads.

Importantly, we can make do with a *single* evaluator for all purposes, with
fairly good performance. In contrast, Agda, Coq and Lean all have multiple
evaluators, and in all cases only the *slowest* evaluators can be used without
restrictions during elaboration. As we'll see in benchmarks, smalltt is robustly
faster than all "slow" evaluators, and can be faster or slower than the Coq
bytecode VM depending on workloads.

#### On hash consing

Hash consing means memoization for certain classes of objects. It is frequently
mentioned as an optimization technique in typechecking. However, specifically
in the context of dependent elaboration, it's not obviously desirable.

Hash consing alone is inadequate for eliminating size explosions. Hash consing
merges duplicate expressions to a single copy. But it does not handle
*beta-reduction* at all, which is a major source of size explosion! For a simple
example, using Peano naturals, it is easy to give a compact definition for
`oneMillion`, involving arithmetic operations. But if I normalize `oneMillion`,
I get a numeral which is incompressible by hash consing.

If I have something like a first-order term language, hash consing can be very
effective. But in dependent type theory, we have higher-order programs with
potentially explosive behavior, and it isn't hard to produce size explosions
even in the presence of full hash-consing. Considering this, and the performance
and complexity overhead of hash consing, I decide to skip it in smalltt.

Hash consing is better suited to more static data, like literals or types in
systems without type-level beta rules, such as simple type theory,
Hindley-Milner or System F. In those cases, hash consing fully captures the
compression which is possible by rewriting along conversion rules.

### Approximate conversion checking

Approximate conversion checking means deciding conversion without computing all
beta-redexes. It's an important feature in pretty much every major TT
implementation. For example, if I again have `oneMillion` as a definition,
checking that `oneMillion` is convertible to itself should immediately return
with success, without unfolding the numeral.

- An important property here is whether a system permits **approximate meta
  solutions**. For example, if I unify `f ?0 = f ?1` where `f` is a defined
  function, I might skip computing the `f` application, and pretend that `f` is
  injective, solving `?0` with `?1`. But if `f` is actually a constant function,
  this causes `?0` and `?1` to be unnecessarily equated. AFAIK Coq and Lean both
  permit approximate solutions, and Agda does not.
- Another property is how **optimistic** the approximation algorithm is. A very
  optimistic algorithm might do the following: if we have identical defined head
  symbols on sides, first we try to unify spines, and if that fails we retry
  with unfolding. This algorithm expects that unifiable values are nearby,
  i.e. reachable after few reductions. The downside of unbounded optimism is
  that recursive backtracking can cause massive slowdown when unifiable values
  are not in fact near.

Smalltt
- Does not allow approximate meta solutions.
- Has bounded approximation: it only performs limited speculation, and
  switches to full reductions on failure.

Concretely, smalltt has three states in unification: "rigid", "flex" and "full".
See `unify` in [src/Unification.hs](src/Unification.hs) for details.

- "Rigid": this is the starting state. In this state we can solve metas, and can
  initiate speculation. Whenever we have the same top-level head symbol on both
  sides, we try unify the spines in "flex" mode, if that fails, we unfold and
  evaluate the sides, and unify them in "full" mode. We stay in "rigid" mode
  when we recurse under canonical type and term formers.
- "Flex": in this state we cannot solve metas, every situation which requires
  a meta solution fails. Moreover, we cannot unfold any top-level definition;
  if we have identical defined head symbols, we can recurse into spines, but
  any situation which requires unfolding also causes failure.
- "Rigid": in this state we can solve metas, and we always immediately unfold
  any defined symbol.

**Example**. We unify `cons oneMillion (cons oneMillion nil)` with
itself. Assume that `cons` and `nil` are rigid term formers for lists.  We start
in rigid mode, which recurses under the `cons`-es, and tries to unify
`oneMillion` with itself twice. Both cases succeed speculatively, because head
symbols match and `oneMillion` is applied to zero arguments.

**Example**. We unify `const ?0 true` with `const false false`, where `const` is
a top-level definition. We start in rigid mode, and since we have `const` head
on both sides, we try to unify spines in flex mode. This fails, since `true /=
false`. So we unfold the `const`-s, and unify sides in"full mode.

In short, smalltt unification backtracks at most once on any path leading to a
subterm ("sub-value" actually, since we recurse on values).

We could have a huge number of different speculative algorithms. A natural
generalization to smalltt is to parametrize the "rigid" state with the number of
shots we get at speculation (smalltt has just one shot). We start in "rigid N"
state, and when a speculative (flex) spine unification fails, we continue in
"rigid (N-1)", and "rigid 0" corresponds to the "full" state. I had this briefly
but did not find much difference in the benchmarks compared to the one-shot
speculation. Alternatively, we could parameterize the "flex" mode with a number
of allowed unfoldings (currently unfolding is not allowed).

I haven't yet done benchmarking on larger, more realistic codebases. The point
is that the current system is compatible with a large number of approximate
conversion checking algorithms, so we could adapt based it on more real-world
performance data. The main limitation is that we can only suspend top-level
unfoldings, and local let-s and immediate local beta-redexes are always
computed.


### Paired values

In infer/check and in unification, instead of using plain values, we use pairs
of values, named `data G = G {g1 :: Val, g2 :: Val}` in the source. Hence,
`unify` takes two `G`-s, and we `infer` returns a `G` for inferred type.

In `G`, the two values are always convertible, but the first value is always the
*least reduced* available version, and the second one is potentially more
reduced.

For example, if we do `check`-ing, the checking type can be headed by a
top-level definition, so we have to compute it until we hit a rigid head symbol,
to see whether it's a Pi type or not. This computation yields a new value which
is more reduced than what we started with. But we don't want to throw away
either of these values! The original version is usually smaller, hence better
for printing and meta solutions, the forced version is more efficient to compute
with, since we don't want to redo the same forcing later.

### Eta-short meta solutions

We prefer to get meta solutions which are as eta-short as
possible. Eta-expansion increases code size and makes evaluation of code slower.

In the standard implementation of syntax-directed function eta-conversion
checking, we do the following:
1. If we have lambdas on both sides, we recurse under binders.
2. If we have a lambda only on one side, we recurse under that lambda, and
   apply the other side to a fresh variable.
3. We only attempt solving metas after we've checked case 2. For example,
   if we have a lambda on one side, and a meta-headed value on the other side,
   first we perform eta-expansion according to step 2.

In smaltt, this is slightly modified to allow eta-short meta solutions.  If we
have a meta on one side, and a non-meta on the other side, we immediately
attempt a solution. However, this can fail if the sides are eta-convertible.
For example, trying to solve `?0` with `λ x. ?0 x` fails because `?0` occurs
rigidly in the solution. So in case of solution failure, we just retry with full
eta expansion. Such failure seems to be very rare in practice, so we almost
always get the eta-short solutions. [This is the place](src/Unification.hs#L386)
where we retry after a failed eta-short solution.

Furthermore, we do additional eta-contraction in pattern unification. We try to
contract meta spines, for example `?0 x y z = ?1 x y z` is contracted to `?0 =
?1`. This is also used in Coq. We have to be careful though not to change
pattern conditions by contraction, e.g. not remove non-linear bound vars by
contraction.

Eta-short solutions are also important for preserving top-level unfoldings.  For
example, assume a function `f : Nat → Nat` defined as a lambda `λ x. t`, where
`t` can be a large definition. If I unify `?0 = f`, the eta-long unification
would solve `?0 := λ x. t x`, while the eta-short version can preserve the `f`
unfolding, and solve simply as `?0 := f`.

### Meta solution checking and quotation

Let's look now at the actual process of generating meta solutions. In basic
pattern unification, we have problems like `?m x₁ x₂ ... xₙ = rhs`, where `?m`
is a meta, `xᵢ` are distinct bound variables, and `rhs` is a value. We aim to
quote `rhs` to a solution term, and at the same time check occurs & scoping
conditions on it.
- Scoping: `rhs` can only depend on `xᵢ` bound variables.
- Occurs: `?0` cannot occur in `rhs` (we assume that rhs is not headed by `?0`).

If both conditions hold, then it is possible to quote `rhs` to some `t` term
which depends only on `xᵢ` bound variables, so that `λ x₁ x₂ ... xₙ. t` is a
well-formed term. In the actual implementation we use a variable [renaming
structure](src/Unification.hs#L35) to map De Bruijn levels in `rhs` to the
correct De Bruijn indices in the output.

The naive implementation beta-normalizes `rhs` while quoting, which we want to
avoid. In smalltt the `rhs` is quoted without unfolding any top-level
definitions or any previously solved meta. However, this is not entirely
straightforward, because the `rhs` conditions should be still checked modulo
full beta-reductions.

We have three different quotation modes, somewhat similarly to what we have seen
in unification, see `flexQuote`, `rigidQuote` and `fullCheck` in
[src/Unification.hs](src/Unification.hs).
- "rigid": the starting mode. We stay in rigid mode when going under
  canonical type/term formers. Illegal var occurrences cause an error to be
  thrown. When we hit an unfolding, we recurse into the spine in flex mode, if
  that returns a possibly invalid term, we check the unfolding in full mode. If
  that succeeds, we learn that the term is actually valid, and return it.
- "flex": this mode returns a boolean flag alongside a term. A true flag means
  that the term is definitely valid, a false means that it is possibly invalid.
  Illegal var occurrences cause a special `Irrelevant` term to be returned along
  with a false flag.
- "full": this mode does not return any term, it just fully evaluates the value
  and throws an error on any illegal var occurrence.

The overall result of this algorithm is that top definitions are *never*
unfolded in any meta solution, but we check validity up to full beta-reduction.
Recall the `?0 = const {Bool}{Bool} true y` example. This yields the `?0`
solution `const {Bool}{Bool} true Irrelevant`. Note that the `Irrelevant` part
disappears during evaluation.

In unification, `Irrelevant` immediately unifies with anything, since it signals
that we are in an irrelevant evaluation context.

It would be better in this case to solve `?0` with `true`. Smalltt does not
bother with performing unfolding for code optimization, but it certainly could;
the primary goal is demonstrate the infrastructure where we have the freedom
to unfold in different ways.

### Meta freezing and approximate occurs checking

"Freezing" metas means that at certain points during elaboration we mark
unsolved metas as unsolvable. This may be used as a performance optimization
and/or a way to enforce meta scoping. All major systems use at least some meta
freezing. No meta freezing would mean that metas are solvable across the whole
program, across module hierarchies.

Smalltt freezes metas like Agda does: a top-level definition together with its
optional type annotation constitutes the elaboration unit where fresh metas are
solvable (but in Agda such blocks can be greatly enlarged through mutually
recursive definitions).

This enforces a scoping invariant: metas can be grouped to mutual blocks before
each top-level definition. Within a mutual block metas can refer to each other
freely, but outside of the block they can only refer to in-scope top defs and
metas in previous blocks.

An **active** meta is in the current meta block. It can be solved or unsolved,
and an unsolved active meta may become solved.

A **frozen** meta is in a previous meta block. A frozen unsolved meta cannot be
solved.

This yields a major optimization opportunity in meta occurs checking: an active
unsolved meta can only occur in the solution of an active meta, but
no other top-level definition! We exploit this in rigid and flex solution
quoting. There, we only look inside solutions of active metas, to do approximate
occurs checking.

For example, assume we're checking for `?m` occurrences, and we hit `?n spine`,
where `?n` is a solved active meta. It is not enough to check `spine`, we also
need to look into the `?n` solution. We do this by simply recursively walking
the *term* solution of `?n`, which may lead to looking into solutions of other
active metas. Here we employ a very simple caching mechanism: we only visit
each active solved meta at most once. So the amount of work done in approximate
occurs checking is limited by the total size of all active meta solutions.

As a result, smalltt is able to very quickly check the classic nested pair
example:

```
dup : {A} → A → Pair A A
 = ...

pairTest =
  let x0  = dup U ;
  let x1  = dup x0;
  let x2  = dup x1;
  ...
  x20
```

At each `dup`, the normal form of the inferred `A` type doubles. In smalltt
this benchmark is technically quadratic, since at each `dup` we search all
previous active solved metas. But these meta solutions are all tiny, they
are of the form `?n := Pair ?(n-1) ?(n-1)`. This takes exponential time
in all tested systems besides smalltt.

More sophisticated caching mechanisms are plausible and probably desirable. For
better UX, it could make sense to combine smarter caching with more relaxed meta
freezing behavior, like allowing metas to be active within a single module.

## GHC-specific optimizations

Smalltt includes some low-level GHC-specific optimizations. These almost
certainly make the code less readable. I included them because
- A very important goal was to have an implementation in *any* language which
  significantly beats all existing systems in elaboration speed. Having concise
  code is *also* a goal, but I care more about the complexity of the underlying
  algorithms, and less about the size of supporting code. The optimization
  boilerplate in smalltt can be easily ignored when we want to look at the core
  algorithms.
- I wanted to at least try some GHC-specific optimizations, to get an idea about
  their impact in the first place. Some of these optimizations turned out to
  have modest impact, but all of them help to some degree.


### Runtime system options

Setting RTS options is important and often overlooked. The performance gains
from the right settings can be easily 30-50%. The default arena size in GHC (1MB
or 4MB starting from GHC 9.2) is very tiny compared to typical RAM sizes. In
smalltt I set the default RTS options to be `-A64M -N8`. This means that
effective arena size is 8 * 64 = 512MB, so smalltt allocates in 512MB chunks. Is
this wasteful?  RAM sizes below 8GB are getting increasingly rare; 512MB is
1/16th of that, and 1/32nd of 16GB. If we can trade RAM for performance, while
still keeping the risk of running out of RAM very low, then we should do it. RAM
exists to be used, not to just sit there.

One of the main reasons why smalltt is compiled with GHC is the RTS performance,
which is overall great. I plan to update my old [normalization
benchmarks](https://github.com/AndrasKovacs/normalization-bench) at some point;
even there GHC performs well, but my newer unstructured benchmarking with newer
GHC versions indicates yet more GHC advantage.

### IO unboxing

This fancy optimization turned out to not have a huge impact on performance, but
I still had to at least implement it and benchmark it, to be able to come to
this conclusion.

In a nutshell, `IO a` blocks the unboxing of `a`. This has been a long-standing
limitation, but fortunately GHC 9.4 will include a fix. I implemented a
workaround of my own which works in GHC 9.0 and 9.2.

[UIO.hs](src/UIO.hs) contains the basic machinery. There's a new `IO` definition
whose operations all require a `CanIO a` constraint on the return value. The
`CanIO` methods use a bunch of levity-polymorphic magic to make this
work. Unfortunately I haven't yet written nicer TH code to derive `CanIO`.
There are only some CPP macros in [src/deriveCanIO.h](src/deriveCanIO.h).

Unboxed `IO` is not a monad but a constrained monad, so I use
[`QualifiedDo`](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/qualified_do.html)
to write `do`-blocks for it. I don't want to wholesale rebind my `do` notation
to constrained monads.

### Custom exceptions

This is the dirtiest trick here. I use custom catching and throwing functions,
to avoid the overhead of the standard type fingerprint mechanism.  See
`Exception#` in [`src/Exceptions.hs`](src/Exceptions.hs). The idea is that My
own primitive `Exception#` type includes the standard typesafe `SomeException`
constructor, but has another one for my own custom exceptions. As a result, I
can catch and throw standard exceptions, but also custom exceptions which have
zero fingerprint overhead. This relies on the ability to silently and unsafely
cast the `SomeException` constructor between the standard `Exception` type and
my `Exception#` type. The memory representation is the same so it works.

I had an old benchmark where custom exceptions had roughly 1/5 the overhead of
standard exceptions. I haven't yet benchmarked both versions in smalltt, I
really should.

### Join-point friendly IO combinators

Sometimes GHC gets confused when we work in standard `IO` or my unboxed `IO`.
Consider code like the following.
```{.haskell}
do foo <- case b of
            True  -> ...
            False -> ...
   bar
```
Let's have the abbreviation `type RW = State# RealWorld#`. `IO` is defined as
```{.haskell}
newtype IO a = IO {unIO :: RW -> (# RW, a #)
```
The mistake that GHC often makes here, is that it pushes the `RW ->` abstraction
under the `case` split, so we get `True -> \s -> ...` in the Core output. As a
result, when this `case` gets turned into a join point, the join point has type
```{.haskell}
(RW -> (# RW, a #)) -> RW -> (# RW, b #)
```
while we would rather have `\s -> case b of True -> ...; False -> ...`, and
the following type for the continuation:
```{.haskell}
a -> RW -> (# RW, b #)
```
This alone is probably not catastrophic, because `RW ->` is erased during
further compilation. But `RW ->` does appear to block a bunch of inlining and
unboxing at the Core level. And with my custom unboxed `IO`, this leads to
failure to inline the monadic binding, which really is catastrophic for
performance.

So I defined the `bind1`-`bind4` combinators in
[`src/UIO.hs`](src/UIO.hs). These seem to reliably fix this issue. You can find
several examples for their usage in [`src/Elaboration.hs`](src/Elaboration.hs).

### Data structures and libraries

#### Hash table

[src/SymTable.hs](src/SymTable.hs) is a custom mutable hash table
implementation, keyed by source position spans. The reason for writing this is
that I have had performance problems with `hashtables`, the primary mutable
hashtable package, where it was outperformed by the immutable `Data.HashMap`,
which should not really happen. However, this was a few years ago, so I should
benchmark my version against alternatives.

I'm also using a custom hash function on bytestrings, which is mostly based on
the non-AES "fallback" hasher in [ahash](https://github.com/tkaitchuck/aHash).

I indent to release in the future a generic variant of my hashtable (which is
not specialized to source span keys) along with my hash function.

#### Libraries

I use the following:
- [`primdata`](https://github.com/AndrasKovacs/primdata): a low-level,
  minimum-overhead array & mutable reference library. It can be viewed as a
  replacement for [`primitive`](https://hackage.haskell.org/package/primitive)
  with a significantly different API.
- [`dynamic-array`](https://github.com/AndrasKovacs/dynamic-array) a small
  dynamic array library, built on the top of `primdata`.
- [`flatparse`](https://github.com/AndrasKovacs/flatparse) a high-performance
  parser combinator library. It is ridiculously faster than all of the parsec
  libraries. The old smalltt versions before the rewrite used `megaparsec`, which
  was about 40 times slower. Parsing speed is now typically 2-3 million LOC/s
  on my system.


## Benchmarks

All files used in benchmarking are available in [bench](bench). The following
programs were used besides smalltt:
- `agda` 2.6.2 with options `-vprofile:7 +RTS -M10G`.
- `coq` 8.13.2, used as `time coqtop -l FILE -batch -type-in-type -time`, or
  dropping the last `-time` options when benchmarking elaboration of large
  files.
- `Lean` 4.0.0 nightly 2021-11-20, commit babcd3563d28. Used as `time lean FILE
  --profile`.

System: Intel 1165G7 CPU, 16GB 3200 MT/s RAM, CPU set to run at 28 W power draw.

**SO** means "stack overflow", and **TL** means "too long". All time figures
are in **seconds**.

Benchmark results are currently in rather crappy hand-pasted markdown tables, I
plan to have nicer graphs here.

There are many benchmark entries marked as N/A. In these cases I haven't yet
been able to reproduce the exact benchmarks in a given system. I expect that
many of these are doable, and I just don't know the right commands or options.


### Elaboration speed

- stlc: Church-coded simply-typed lambda calculus plus some internal definitions.
  Fairly heavy in terms of sizes of types and number of metavariables. Comes
  in 5k and 10k LOC versions, where everything is renamed and copied many times.
- stlcLessImpl: a lighter version, with no implicit arguments inside stlc algebras.
  This works in Coq, while the heavier version does not, because Coq does not support
	  higher-order implicit arguments.
- stlcSmall: an even lighter version which only includes variables, lambdas and
  applications in the object language. For fun, I also test files with one million
  lines of code. I don't include these files in the repo, because they're around
  50MB each. They can be generated by running `stlcSmall1M` functions from
  [src/GenTestFiles.hs](src/GenTestFiles.hs).
- Agda 2.6.2 has a parsing blowup issue on large files:
  https://github.com/agda/agda/issues/5670. So only `stlc`, `stlcLessImpl`, and
  `stlcSmall` are indicative of elaboration performance.


|                 | smalltt | Agda    | Coq    | Lean elab |  Lean total |
|-----------------|---------|---------|--------|-----------|-------------|
| stlc            | 0.014   | 0.573   | N/A    | 0.075     |  0.194      |
| stlc5k          | 0.179   | 4.127   | N/A    | 2.97      |  6.049      |
| stlc10k         | 0.306   | 16.160  | N/A    | 6.21      |  12.982     |
| stlcLessImpl    | 0.008   | 0.358   | 0.151  | 0.052     |  0.166      |
| stlcLessImpl5k  | 0.140   | 4.169   | 0.905  | 2.15      |  4.508      |
| stlcLessImpl10k | 0.275   | 17.426  | 1.703  | 4.24      |  8.861      |
| stlcSmall       | 0.003   | 0.106   | 0.128  | 0.015     |  0.073      |
| stlcSmall5k     | 0.037   | 4.445   | 0.809  | 1.38      |  2.649      |
| stlcSmall10k    | 0.072   | 22.8    | 1.470  | 2.76      |  5.244      |
| stlcSmall1M     | 8.725   | TL      | 439.3  | 317       |  615        |


### Elaboration asymptotics

See the `asymptotics` files.
- idTest: `id id ... id`, 40 times iterated.
- pairTest: 30 times nested pairs using local `let`.
- vecTest: length-indexed vector with 960 elements.

We separately consider elaboration time and total command time, because
serialization often takes a quadratic hit on vecTest.

|               | smalltt | Agda elab | Agda total | Coq elab | Coq total | Lean elab | Lean total
|---------------|---------|-----------|--------|---------|-------|---------|-------|
| idTest        | 0.000   | TL        | TL     | TL      | TL    | TL      | TL    |
| pairTest      | 0.000   | TL        | TL     | TL      | TL    | TL      | TL    |
| vecTest       | 0.078   | 1.128     | 4.098  | 0.769   | 0.935 | 0.244   | 3.65  |

- smalltt is also quadratic on vecTest! But it's fast enough to be a
  non-issue. The quadratics comes from the occurs checking, which visits a
  linear number of active metas for each cons cell. Making it overall linear is
  possible, but it would require smarter meta occurs caching.
- Lean elaboration is actually linear on pairTest, but the task itself does not
  finish, because the "compilation" phase is exponential.


### Raw conversion checking

See the `conv_eval` files.
- NatConv: conversion checking Church Peano numerals of given size
- TreeConv: conversion checking complete Church binary trees of given depth
- TreeConvM: same but sides contain unsolved metas.

|               | smalltt | Agda    | Coq    | Lean    |
|---------------|---------|---------|--------|---------|
|NatConv1M      |0.045    | 1.8    | SO     | SO      |
|NatConv5M      |0.188    | 9.6    | SO     | SO      |
|NatConv10M     |0.712    | 19.7   | SO     | SO      |
|TreeConv15     |0.055    | 0.016  | 0.006  | 0.020   |
|TreeConv18     |0.088    | 0.02   | 0.008  | 0.020   |
|TreeConv19     |0.161    | 0.03   | 0.007  | 0.020   |
|TreeConv20     |0.408    | 1.7    | 0.612  | 20.7    |
|TreeConv21     |0.834    | 3.4    | 1.168  | 29.3    |
|TreeConv22     |1.722    | 6.4    | 2.347  | 29.8    |
|TreeConv23     |3.325    | 13.7   | 4.731  | 28.8    |
|TreeConvM15    |0.010    | 0.770  | 0.006  | N/A     |
|TreeConvM18    |0.092    | 6.35   | 0.007  | N/A     |
|TreeConvM19    |0.169    | 12.8   | 0.005  | N/A     |
|TreeConvM20    |0.361    | 26.6   | 0.549  | N/A     |
|TreeConvM21    |0.835    | 50.8   | 1.248  | N/A     |
|TreeConvM22    |1.694    | TL     | 2.704  | N/A     |
|TreeConvM23    |3.453    | TL     | 5.515  | N/A     |

- The TreeConvM benchmarks fail to elaborate in Lean, for some reason we get
  "can't synthesize placeholder" errors, although the metas should be solvable.
- Note that Agda, Coq and Lean all have more aggressive approximate conversion
  checking than smalltt, since they can shortcut the task up to TreeConv19. Coq
  can even do this up for TreeConvM15-19; this requires *approximate meta
  solutions*. It's apparent that Agda does not do such solutions.
- Lean performance is puzzling, there seems to be a large constant overhead.
- Agda performance degrades sharply when we throw metas in the mix.

### Raw evaluation and normalization

See the `conv_eval` files again.
- ForceTree : fold over a binary tree with Boolean conjunction
- NfTree    : normalize a tree

|               | smalltt | Agda    | Coq vm_compute | Coq compute | Coq lazy    |Lean reduce | Lean eval |
|---------------|---------|---------|----------------|-------------|-------------|------------|-----------|
|ForceTree15    |0.011   | 0.070    | 0.002          | 0.023       | 0.053       | N/A        | 0.022     |
|ForceTree18    |0.100   | 0.47     | 0.019          | 0.172       | 0.295       | N/A        | 0.172     |
|ForceTree19    |0.240   | 0.92     | 0.041          | 0.308       | 0.74        | N/A        | 0.341     |
|ForceTree20    |0.487   | 1.8      | 0.078          | 0.818       | 1.179       | N/A        | 0.681     |
|ForceTree21    |1.070   | 3.58     | 0.152          | 1.237       | 2.293       | N/A        | 1.77      |
|ForceTree22    |2.122   | 7.37     | 0.301          | 2.486       | 4.601       | N/A        | 2.72      |
|ForceTree23    |4.372   | 15.93    | 0.747          | 5.544       | 9.658       | N/A        | 5.76      |
|NfTree15       |0.005   | N/A      | 0.028          | 0.013       | 0.01        | N/A        | N/A       |
|NfTree18       |0.064   | N/A      | 0.192          | 0.128       | 0.213       | N/A        | N/A       |
|NfTree19       |0.111   | N/A      | 0.525          | 0.293       | 0.404       | N/A        | N/A       |
|NfTree20       |0.259   | N/A      | 0.718          | 0.635       | 0.806       | N/A        | N/A       |
|NfTree21       |0.552   | N/A      | 1.573          | 1.197       | 1.508       | N/A        | N/A       |
|NfTree22       |1.286   | N/A      | 2.962          | 2.952       | 3.15        | N/A        | N/A       |
|NfTree23       |3.023   | N/A      | 5.975          | 5.03        | 7.271       | N/A        | N/A       |

- Agda NfTree is N/A because there is no way to force normal forms in Agda
  without printing them.
- Lean reduce is N/A because for ForceTree it throws a recursion depth error
  which I can't get rid of, and for NfTree it's the same as in Agda.
- Lean eval is N/A for the same reason, but it also asks for a missing "Eval
  Tree" instance. Apparently only such types can be evaluted, but I don't know
  how to write an instance for it.
- On performance:
  - Coq vm_compute is extremely strong in ForceTree, which is a fairly lightly
    allocating workload. I note that smalltt with glued evaluation disabled
    would be 2x faster here, but that would be still just the third of Coq VM
    performance.
  - On the other hand, smalltt is faster in normalization, a more
    allocation-heavy task. I attribute this to superior RTS performance.
  - Coq compute and lazy are always behind smalltt.
  - Lean eval is behind smalltt, even though it's strict, closed, bytecode
    interpreter, while smalltt is a partially lazy, open, AST interpreter.
