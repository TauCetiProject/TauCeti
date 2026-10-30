/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# The fundamental inequality on a number field

Let `K` be a number field and `α ∈ K` nonzero. In Mathlib's relative normalization the local
factor of `α` at an infinite place `v` is `v α ^ v.mult` and at a finite place it is `v α`, and
the multiplicative height is the product of the truncations `max (v α) 1` of these factors over
all places. This file records the opposite truncation and what it gives on a finite set of
places, which is the local input of Liouville's inequality and of the proofs of Roth's theorem
and the Subspace Theorem.

The truncations `min 1 (v α)` of the local factors of `α`, taken over all places, multiply to
exactly `(mulHeight₁ α)⁻¹`: this is the product formula, read through
`min 1 t = (max t⁻¹ 1)⁻¹` and `mulHeight₁ α⁻¹ = mulHeight₁ α`. Each truncated factor is at most
`1`, so cutting the product down to finite sets `Sinf` of infinite places and `Sfin` of finite
places can only increase it. This is the **fundamental inequality**
`(mulHeight₁ α)⁻¹ ≤ ∏ v ∈ S, min 1 (v α)`: an element of `K` cannot be small at the places of
`S` unless its height is large. Dually, the factors `max (v α) 1` over `Sinf` and `Sfin` multiply
to at most `mulHeight₁ α`, so the untruncated local factors over `S` lie between
`(mulHeight₁ α)⁻¹` and `mulHeight₁ α`.

Everything is stated with Mathlib's typed places `InfinitePlace K` and `FinitePlace K`, the
vocabulary of `NumberField.mulHeight₁_eq` and `NumberField.prod_abs_eq_one`. At a single place
the bounds are the multiplicative reading of
`TauCeti.GlobalNumberFields.abs_log_normalizedAbsValue_le_logHeight₁`, which is stated for the
normalized absolute values on the combined carrier of places.

## Main results

* `NumberField.prod_min_one_apply_eq_inv_mulHeight₁`: the truncated local factors of `α ≠ 0`
  over all places multiply to `(mulHeight₁ α)⁻¹`.
* `NumberField.inv_mulHeight₁_le_prod_min_one_apply`: the fundamental inequality, the same
  product over finite sets of places is at least `(mulHeight₁ α)⁻¹`.
* `NumberField.prod_max_apply_one_le_mulHeight₁`: the factors `max (v α) 1` over finite sets of
  places multiply to at most `mulHeight₁ α`.
* `NumberField.inv_mulHeight₁_le_prod_apply` and `NumberField.prod_apply_le_mulHeight₁`: the
  product of the local factors of `α` over finite sets of places lies between
  `(mulHeight₁ α)⁻¹` and `mulHeight₁ α`.
* `NumberField.InfinitePlace.inv_mulHeight₁_le_min_one_apply`,
  `NumberField.InfinitePlace.max_apply_one_le_mulHeight₁` and their `FinitePlace` counterparts:
  the bounds at a single place.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press,
  2006, §1.5, (1.8) and Theorem 1.5.21.
-/

public section

open Finset Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
/-- At an absolute value `v`, the truncation `min 1 (v α)` of `α ≠ 0` is the inverse of the
truncation `max (v α⁻¹) 1` of `α⁻¹`; this turns the truncated local factors of `α` into the
inverses of the local factors of the height of `α⁻¹`. -/
private lemma min_one_apply_eq_inv_max_apply_inv_one (v : AbsoluteValue K ℝ) {α : K}
    (hα : α ≠ 0) : min 1 (v α) = (max (v α⁻¹) 1)⁻¹ := by
  have ht : 0 < v α := v.pos hα
  rw [map_inv₀]
  rcases le_total (v α) 1 with h | h
  · rw [min_eq_right h, max_eq_left ((one_le_inv₀ ht).2 h), inv_inv]
  · rw [min_eq_left h, max_eq_right ((inv_le_one₀ ht).2 h), inv_one]

/-- **The product formula for the truncated local factors.** For `α ≠ 0`, the truncations
`min 1 (v α)` of the local factors of `α` over all places of `K` multiply to `(mulHeight₁ α)⁻¹`.
For `α = 0` the left side is `0` while the height is `1`. -/
theorem prod_min_one_apply_eq_inv_mulHeight₁ {α : K} (hα : α ≠ 0) :
    (∏ v : InfinitePlace K, min 1 (v α) ^ v.mult) * ∏ᶠ v : FinitePlace K, min 1 (v α) =
      (mulHeight₁ α)⁻¹ := by
  rw [← mulHeight₁_inv, mulHeight₁_eq, mul_inv, ← prod_inv_distrib, ← finprod_inv_distrib]
  simp only [InfinitePlace.coe_apply, FinitePlace.coe_apply,
    min_one_apply_eq_inv_max_apply_inv_one _ hα, inv_pow]

/-- The factors `max (v α) 1` over a finite set `Sinf` of infinite places, with the weights
`v.mult`, and a finite set `Sfin` of finite places multiply to at most `mulHeight₁ α`. -/
theorem prod_max_apply_one_le_mulHeight₁ (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (α : K) :
    (∏ v ∈ Sinf, max (v α) 1 ^ v.mult) * ∏ v ∈ Sfin, max (v α) 1 ≤ mulHeight₁ α := by
  classical
  have hf : (fun v : FinitePlace K ↦ max (v α) 1).HasFiniteMulSupport := by
    rcases eq_or_ne α 0 with rfl | hα
    · simp [Function.HasFiniteMulSupport]
    · exact .max (FinitePlace.hasFiniteMulSupport hα) Function.hasFiniteMulSupport_one
  -- The finite product over all finite places is a product over `Sfin` and the support.
  rw [mulHeight₁_eq, finprod_eq_prod_of_mulSupport_toFinset_subset _ hf
    (subset_union_right (s₁ := Sfin))]
  -- Every factor is at least `1`, so enlarging either set of places can only increase it.
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · exact prod_le_prod_of_subset_of_one_le₀ (subset_univ _) (fun _ _ ↦ by positivity)
      fun _ _ _ ↦ one_le_pow₀ (le_max_right _ _)
  · exact prod_le_prod_of_subset_of_one_le₀ subset_union_left (fun _ _ ↦ by positivity)
      fun _ _ _ ↦ le_max_right _ _

/-- **The fundamental inequality.** For `α ≠ 0`, the truncations `min 1 (v α)` of the local
factors of `α` over a finite set `Sinf` of infinite places, with the weights `v.mult`, and a
finite set `Sfin` of finite places multiply to at least `(mulHeight₁ α)⁻¹`. -/
theorem inv_mulHeight₁_le_prod_min_one_apply (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) {α : K} (hα : α ≠ 0) :
    (mulHeight₁ α)⁻¹ ≤ (∏ v ∈ Sinf, min 1 (v α) ^ v.mult) * ∏ v ∈ Sfin, min 1 (v α) := by
  have h := prod_max_apply_one_le_mulHeight₁ Sinf Sfin α⁻¹
  rw [mulHeight₁_inv] at h
  have hpos : 0 < (∏ v ∈ Sinf, max (v α⁻¹) 1 ^ v.mult) * ∏ v ∈ Sfin, max (v α⁻¹) 1 := by
    positivity
  calc (mulHeight₁ α)⁻¹
      ≤ ((∏ v ∈ Sinf, max (v α⁻¹) 1 ^ v.mult) * ∏ v ∈ Sfin, max (v α⁻¹) 1)⁻¹ :=
        inv_anti₀ hpos h
    _ = (∏ v ∈ Sinf, min 1 (v α) ^ v.mult) * ∏ v ∈ Sfin, min 1 (v α) := by
        rw [mul_inv, ← prod_inv_distrib, ← prod_inv_distrib]
        simp only [InfinitePlace.coe_apply, FinitePlace.coe_apply,
          min_one_apply_eq_inv_max_apply_inv_one _ hα, inv_pow]

/-- The local factors of `α ≠ 0` over a finite set `Sinf` of infinite places, with the weights
`v.mult`, and a finite set `Sfin` of finite places multiply to at least `(mulHeight₁ α)⁻¹`. -/
theorem inv_mulHeight₁_le_prod_apply (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) {α : K} (hα : α ≠ 0) :
    (mulHeight₁ α)⁻¹ ≤ (∏ v ∈ Sinf, v α ^ v.mult) * ∏ v ∈ Sfin, v α := by
  refine (inv_mulHeight₁_le_prod_min_one_apply Sinf Sfin hα).trans ?_
  gcongr <;> exact min_le_right _ _

/-- The local factors of `α` over a finite set `Sinf` of infinite places, with the weights
`v.mult`, and a finite set `Sfin` of finite places multiply to at most `mulHeight₁ α`. -/
theorem prod_apply_le_mulHeight₁ (Sinf : Finset (InfinitePlace K))
    (Sfin : Finset (FinitePlace K)) (α : K) :
    (∏ v ∈ Sinf, v α ^ v.mult) * ∏ v ∈ Sfin, v α ≤ mulHeight₁ α := by
  refine le_trans ?_ (prod_max_apply_one_le_mulHeight₁ Sinf Sfin α)
  gcongr <;> exact le_max_left _ _

namespace InfinitePlace

/-- At an infinite place `v`, the truncated local factor `min 1 (v α) ^ v.mult` of `α ≠ 0` is
at least `(mulHeight₁ α)⁻¹`. -/
theorem inv_mulHeight₁_le_min_one_apply_pow_mult (v : InfinitePlace K) {α : K} (hα : α ≠ 0) :
    (mulHeight₁ α)⁻¹ ≤ min 1 (v α) ^ v.mult := by
  simpa using inv_mulHeight₁_le_prod_min_one_apply {v} ∅ hα

/-- At an infinite place `v`, `min 1 (v α)` is at least `(mulHeight₁ α)⁻¹` for `α ≠ 0`. -/
theorem inv_mulHeight₁_le_min_one_apply (v : InfinitePlace K) {α : K} (hα : α ≠ 0) :
    (mulHeight₁ α)⁻¹ ≤ min 1 (v α) :=
  (v.inv_mulHeight₁_le_min_one_apply_pow_mult hα).trans <|
    pow_le_of_le_one (by positivity) (min_le_left _ _) v.mult_ne_zero

/-- At an infinite place `v`, the factor `max (v α) 1 ^ v.mult` of the height of `α` is at most
`mulHeight₁ α`. -/
theorem max_apply_one_pow_mult_le_mulHeight₁ (v : InfinitePlace K) (α : K) :
    max (v α) 1 ^ v.mult ≤ mulHeight₁ α := by
  simpa using prod_max_apply_one_le_mulHeight₁ {v} ∅ α

/-- At an infinite place `v`, `max (v α) 1` is at most `mulHeight₁ α`. -/
theorem max_apply_one_le_mulHeight₁ (v : InfinitePlace K) (α : K) :
    max (v α) 1 ≤ mulHeight₁ α :=
  (le_self_pow₀ (le_max_right _ _) v.mult_ne_zero).trans (v.max_apply_one_pow_mult_le_mulHeight₁ α)

end InfinitePlace

namespace FinitePlace

/-- At a finite place `v`, the truncated local factor `min 1 (v α)` of `α ≠ 0` is at least
`(mulHeight₁ α)⁻¹`. -/
theorem inv_mulHeight₁_le_min_one_apply (v : FinitePlace K) {α : K} (hα : α ≠ 0) :
    (mulHeight₁ α)⁻¹ ≤ min 1 (v α) := by
  simpa using inv_mulHeight₁_le_prod_min_one_apply ∅ {v} hα

/-- At a finite place `v`, the factor `max (v α) 1` of the height of `α` is at most
`mulHeight₁ α`. -/
theorem max_apply_one_le_mulHeight₁ (v : FinitePlace K) (α : K) :
    max (v α) 1 ≤ mulHeight₁ α := by
  simpa using prod_max_apply_one_le_mulHeight₁ ∅ {v} α

end FinitePlace

end NumberField
