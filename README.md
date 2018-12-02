# smalltt

See "Demo.stt" for notes on usage, and a demo.


### Design & goals

- Higher-order unification, implicit arguments type-in type.
- Scoping:
  + There is a distinguished top-level scope.
  + Postulates are only allowed on top-level (as well as possible inductive type declarations).
  + Local let-definitions are allowed.
  + No modules at this stage.

- Simplified sharing-preserving elaboration:
  + Metas live in the distinguished top-level scope: for every top-level binding
    group, there is a top-level mutual block of meta bindings. Meta solutions
    can refer to any previous meta, or any meta in the same meta block. Meta
    solutions can also refer to previous top-level definitions and postulates.
  + Metas abstract over local bound variables, but not local let-definitions.
  + Hence, local let-definitions must be unfolded in meta solutions.
  + We have glued evaluation with respect to the current top-level scope position. I.e.
    the glued evaluator doesn't unfold top-level definitions, including solved metas.
  + The great simplification compared to my previous designs is that metas never
    move in scope, and are never generalized over binders.
  + Elaboration output will be a bit uglier, since metas will typically have
    superfluous abstractions.
  + Sharing would be also worse, because the extra variable abstractions prevent
    meta solutions from being call-by-need memoized.
  + Shadowing is allowed.
  + We throw error if there are unsolved metas after a top-level entry elab. Hence,
    unsolved frozen metas are not possible and we don't check for them.


### TODO Supporting libraries

- Replacement for *primitive* (which is incomplete and annoyingly verbose):
  + Three classes or runtime objects: boxed, unboxed, unlifted.
  + Arrays, smallarrays, unifted arrays, small unlifted arrays, unboxed arrays.
  + Unlifted mutable refs, unboxed mutable refs implemented as arrays.
  + Lazy identity monad for semi-strictness.
  + Semi-strict indexing support for every array/ref type.
  + runRW#-based unsafePerform.
  + Convenience functions for directly working with arrays.
  + Slices on top of arrays.
