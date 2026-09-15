/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Basic.Countable.Basic

/-!
# Matrices over a countable type, with finitely many entries, are countable

`Matrix m n α` is a semireducible definition rather than an abbreviation, so instance synthesis
does not see through it to the underlying `m → n → α`: `Countable (m → n → α)` resolves and
`Countable (Matrix m n α)` does not. This is the same reason Mathlib states the `Matrix` algebraic
instances explicitly rather than inheriting them from `Pi`.

## Main results

* `Matrix.instCountable`: `Matrix m n α` is countable for finite index types and countable entries.
-/

public section

variable {m n α : Type*}

/-- Matrices indexed by finite types, with entries in a countable type, form a countable type.

Stated because `Matrix` does not unfold during instance synthesis; the proof is just the
corresponding fact for its underlying function type. -/
instance Matrix.instCountable [Finite m] [Finite n] [Countable α] :
    Countable (Matrix m n α) :=
  inferInstanceAs (Countable (m → n → α))
