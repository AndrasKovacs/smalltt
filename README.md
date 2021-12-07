
# smalltt

### Overview

This project serves as a demo for several techniques for high-performance
elaboration with dependent types. I also include some benchmarks, which are
intended to be as similar as possible across Agda, Lean, Coq and smalltt.

Work in progress. Code and documentation alike may be subject to change, cleanup
or extension.

Broadly speaking, I have two kinds of potentially interesting features.

1. [High-level design features](#design) in elaboration. This could be interesting to a
   general audience of language implementors.
2. [GHC-specific tricks](#haskell-specific-optimizations), libraries and
   optimizations.

Both are documented here in more detail.

I admit that throwing in "dirty" GHC-specific optimizations makes the code less
readable, but since comparative benchmarking is an important goal here, I wanted
to make sure that I don't leave significant performance on the table. Most of
the tricks are just workarounds for GHC-specific limitations, and could be
omitted when working in a different language. You may ask: why work in Haskell?
While Haskell has weak points, it also has several valuable strong points,
especially the runtime system performance for our typical workloads. I discuss
this in more detail in the section on [Haskell-specific
optimizations](#haskell-specific-optimizations).

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
tactics) to introduce pathological cases.

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
unfolding the definition, and not unfolding it. This has a moderate constant
overhead during evaluation. Later, the quotation function has the choice of
visiting either evaluation branches, or both, in which case as much as possible
computation is shared between the branches.

When we need high-performance evaluation during conversion checking, we have it,
and when we solve a metavariable, we are able to quote values to terms which are
*minimal* with respect to top-level unfolding. This is also useful in error
message reporting and interaction, where we want to be able to display small
terms.

Only being able to control top-level unfolding is not quite sufficient for
sophisticated interactive proving, but the technique here could be extended
to richer unfolding control with modest additional overheads.

<!-- Importantly, we only need a *single* evaluator for all purposes. Contrast the -->
<!-- following: -->

<!-- - Agda has a slow evaluator and a separate, faster abstract machine. The latter -->
<!--   cannot be used during conversion checking if there are metavariables in the -->
<!--   involved terms. Both are written in Haskell and interpret AST. -->
<!-- - Coq has an AST interpreter written in OCaml, a separate bytecode VM written in -->
<!--   C, and also a native code compiler (compiling to OCaml). Of these, only the -->
<!--   OCaml reducer can handle metavariables. -->
<!-- - Lean 4 has a kernel AST interpreter, a bytecode interpreter, and a native code -->
<!--   backend. Of these, only the kernel interpreter can be used generally during -->
<!--   elaboration. -->

<!-- TODO: perf remarks -->

#### On hash consing

Hash consing means memoization for certain classes of objects. It is frequently
brought up as an optimization technique in typechecking. However, specifically
in the context of dependent elaboration, I prefer to not use hash consing.

First, hash consing alone is inadequate for eliminating size explosions. Hash
consing merges duplicate expressions to a single copy. But it does not handle
*beta-reduction* at all, which is a major source of size explosion! For a simple
example, using Peano naturals, it is easy to give a compact definition for
`oneMillion`, involving arithmetic operations. But if I normalize `oneMillion`,
I get a numeral which is incompressible by hash consing.

If I have something like a first-order term language, hash consing can be very
effective. But in dependent type theory, we have higher-order programs with
potentially explosive behavior, and it isn't hard to produce size explosions
even in the presence of full hash-consing. Considering this, and the performance
and complexity overhead of hash consing, I choose to not do hash consing in
smalltt.

### Approximate conversion checking

Non-deterministic unfolding


## Haskell-specific optimizations
