/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Points on the conics `a² + δ b² = 1`

Over a field `K` the conic `a² + δ b² = 1` always has the points `(±1, 0)`. This file shows that
over an infinite field in which `2 ≠ 0` it also has a point with both coordinates nonzero, for
every `δ`. The rational parametrisation `t ↦ ((1 - δ t²) / (1 + δ t²), 2t / (1 + δ t²))` gives such
a point for every `t` with `t ≠ 0` and `δ t² ≠ ±1`, and these exclusions are the roots of a nonzero
polynomial, so an infinite field has admissible `t`.

Neither hypothesis can be dropped: in characteristic two `a² + b² δ = (a + b √δ)²`, so over
`𝔽₂(δ)` the only solutions have `b = 0`, and over `𝔽₃` the circle `a² + b² = 1` has no point with
both coordinates nonzero.

The statement is what makes a binary form `⟨1, δ⟩` represent `1` with both coordinates nonzero; it
supplies the even unitary units `a + b • ω` outside the Lipschitz group in
`TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six.lean`.

## Main results

* `TauCeti.exists_sq_add_sq_mul_eq_one`: the conic `a² + b² δ = 1` has a point with both
  coordinates nonzero over every infinite field in which `2 ≠ 0`.
-/

public section

namespace TauCeti

open Polynomial

/-- **The conic `a² + b² δ = 1` has a point with both coordinates nonzero over every infinite field
in which `2 ≠ 0`.** -/
theorem exists_sq_add_sq_mul_eq_one {K : Type*} [Field K] [Infinite K] [NeZero (2 : K)] (δ : K) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ a ^ 2 + b ^ 2 * δ = 1 := by
  -- The rational parametrisation `t ↦ ((1 - δt²)/(1 + δt²), 2t/(1 + δt²))` works whenever `t ≠ 0`
  -- and `δt² ≠ ±1`, that is, away from the roots of the nonzero polynomial
  -- `X (1 - δ X²) (1 + δ X²)`; an infinite field has a non-root
  -- (`Polynomial.finite_setOfPred_isRoot`).
  have hp : (X * (1 - C δ * X ^ 2) * (1 + C δ * X ^ 2) : K[X]) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero X_ne_zero ?_) ?_ <;>
    · intro h
      simpa using congrArg (coeff · 0) h
  obtain ⟨t, ht⟩ := (finite_setOfPred_isRoot hp).infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, IsRoot.def, eval_mul, eval_X, eval_sub, eval_add,
    eval_one, eval_C, eval_pow, mul_eq_zero, not_or] at ht
  obtain ⟨⟨ht0, h₂⟩, h₁⟩ := ht
  refine ⟨(1 - δ * t ^ 2) / (1 + δ * t ^ 2), 2 * t / (1 + δ * t ^ 2), div_ne_zero h₂ h₁,
    div_ne_zero (mul_ne_zero two_ne_zero ht0) h₁, ?_⟩
  field_simp
  ring

end TauCeti
