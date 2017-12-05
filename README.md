# smalltt

Small type theory implementation. You can take a look at "examples.stt" for examples and description
of syntax & features.

Currently, we have
  - Type-in-type
  - Higher-order unification
  - Bidirectional elaboration
  - Positional & named implicit arguments
  - Some control over metavariable insertion
  - Tolerable error messages with source locations

Missing things which I'll perhaps add

  - Named holes which cause goal & assumption types to be displayed on file load
  - Type-annotated lambdas
  - Sigmas
  - More unification: pruning, intersections, eta-contractions, dependency erasure
  - Acceptable pretty printing with at least toggleable implicit args
  - Unreduced "glued" elaboration contexts, and what it enables: approximate conversion checks + nicer printed terms
  - Inductive-inductive types via eliminators

Non-goals
  - Noteworthy time/space optimizations for elaboration
  - Performant implementation & data structures
  - Idiomatic Haskell
  - Proper universes
  - Modules
  - Constraint postponing
