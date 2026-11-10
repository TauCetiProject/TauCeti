/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Points on the conics `a² + δ b² = 1`

Over a field `K` the conic `a² + δ b² = 1` always has the points `(±1, 0)`. This file shows that
over a field with more than five elements in which `2 ≠ 0` it also has a point with both
coordinates nonzero, for every `δ`. The rational parametrisation
`t ↦ ((1 - δ t²) / (1 + δ t²), 2t / (1 + δ t²))` gives such a point for every `t` with `t ≠ 0` and
`δ t² ≠ ±1`, and these exclusions are the roots of a nonzero polynomial of degree at most five, so
a field with more than five elements has admissible `t`.

Neither hypothesis can be weakened: in characteristic two `a² + b² δ = (a + b √δ)²`, so over
`𝔽₂(δ)` the only solutions have `b = 0`, and over `𝔽₃` and `𝔽₅` the circle `a² + b² = 1` has no
point with both coordinates nonzero. In particular the result holds over every infinite field in
which `2 ≠ 0`.

The statement is what makes a binary form `⟨1, δ⟩` represent `1` with both coordinates nonzero; it
supplies the even unitary units `a + b • ω` outside the Lipschitz group in
`TauCeti/LinearAlgebra/CliffordAlgebra/Spin/LowRank/Six/Basic.lean`.

## Main results

* `TauCeti.exists_sq_add_sq_mul_eq_one`: the conic `a² + b² δ = 1` has a point with both
  coordinates nonzero over every field with more than five elements in which `2 ≠ 0`.
-/

public section

namespace TauCeti

open Cardinal Polynomial

/-- **The conic `a² + b² δ = 1` has a point with both coordinates nonzero over every field with
more than five elements in which `2 ≠ 0`.** -/
theorem exists_sq_add_sq_mul_eq_one {K : Type*} [Field K] [NeZero (2 : K)] (hK : 5 < #K) (δ : K) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ a ^ 2 + b ^ 2 * δ = 1 := by
  -- The rational parametrisation `t ↦ ((1 - δt²)/(1 + δt²), 2t/(1 + δt²))` works whenever `t ≠ 0`
  -- and `δt² ≠ ±1`, that is, away from the roots of the nonzero polynomial
  -- `X (1 - δ X²) (1 + δ X²)` of degree at most five; a field with more than five elements has a
  -- non-root (`Polynomial.exists_eval_ne_zero_of_natDegree_lt_card`).
  have hp : (X * (1 - C δ * X ^ 2) * (1 + C δ * X ^ 2) : K[X]) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero X_ne_zero ?_) ?_ <;>
    · intro h
      simpa using congrArg (coeff · 0) h
  have hdeg : (X * (1 - C δ * X ^ 2) * (1 + C δ * X ^ 2) : K[X]).natDegree ≤ 5 := by
    compute_degree
  obtain ⟨t, ht⟩ := exists_eval_ne_zero_of_natDegree_lt_card _ hp <|
    (Nat.cast_le.2 hdeg).trans_lt (by exact_mod_cast hK)
  simp only [eval_mul, eval_X, eval_sub, eval_add, eval_one, eval_C, eval_pow, ne_eq,
    mul_eq_zero, not_or] at ht
  obtain ⟨⟨ht0, h₂⟩, h₁⟩ := ht
  refine ⟨(1 - δ * t ^ 2) / (1 + δ * t ^ 2), 2 * t / (1 + δ * t ^ 2), div_ne_zero h₂ h₁,
    div_ne_zero (mul_ne_zero two_ne_zero ht0) h₁, ?_⟩
  field_simp
  ring

end TauCeti
