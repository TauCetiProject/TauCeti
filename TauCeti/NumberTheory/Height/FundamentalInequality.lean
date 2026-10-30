/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Height.NumberField

import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.NumberTheory.NumberField.FinitePlace

/-!
# The fundamental inequality

Let `K` be a number field and `x ≠ 0` an element of `K`. Multiply the local factors of `x` over a
finite set `S∞` of infinite places, weighted by `InfinitePlace.mult`, and a finite set `S₀` of
finite places. The **fundamental inequality** traps the result between the multiplicative height
of `x` and its reciprocal:

```text
(mulHeight₁ x)⁻¹ ≤ (∏ v ∈ S∞, |x|_v ^ mult v) * ∏ v ∈ S₀, |x|_v ≤ mulHeight₁ x.
```

The upper bound holds for `x = 0` as well. The lower bound follows from the upper bound for
`x⁻¹`, since inversion inverts the product and preserves the height (`Height.mulHeight₁_inv`).

In the form used by Liouville's inequality and Roth's theorem, every local factor is truncated
to `min 1 |x|_v` and the product is taken over **all** places. Then it is exactly
`(mulHeight₁ x)⁻¹`, because `min 1 t * max t 1 = t` turns the product formula into the definition
of the height. Every truncated factor is at most `1`, so cutting the product down to `S∞` and `S₀`
can only increase it. At a single place the two bounds read
`(mulHeight₁ x)⁻¹ ≤ min 1 |x|_v` and `max |x|_v 1 ≤ mulHeight₁ x`.

## Main results

* `NumberField.prod_apply_le_mulHeight₁` and `NumberField.inv_mulHeight₁_le_prod_apply`: the two
  halves of the fundamental inequality.
* `NumberField.prod_min_one_apply_eq_inv_mulHeight₁`: over all places the truncated local factors
  of `x ≠ 0` multiply to `(mulHeight₁ x)⁻¹`.
* `NumberField.inv_mulHeight₁_le_prod_min_one_apply`: over finitely many places the truncated
  product is at least `(mulHeight₁ x)⁻¹`.
* `NumberField.InfinitePlace.max_apply_one_le_mulHeight₁`,
  `NumberField.FinitePlace.max_apply_one_le_mulHeight₁`,
  `NumberField.InfinitePlace.inv_mulHeight₁_le_min_one_apply` and
  `NumberField.FinitePlace.inv_mulHeight₁_le_min_one_apply`: the bounds at a single place.

The logarithmic form of the single-place bounds, for the normalized absolute value at a place, is
`TauCeti.GlobalNumberFields.abs_log_normalizedAbsValue_le_logHeight₁`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §1.5, the fundamental inequality (1.8).

The same statements, along the same route, are formalized in Ralf Stephan's
`rwst/Subspace-Theorems` at `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file
`DiophantineApproximation/FundamentalInequality.lean` (Apache 2.0).
-/

public section

open Height

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

variable (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))

/-! ### The fundamental inequality -/

/-- **The fundamental inequality, upper bound** (Bombieri–Gubler (1.8)): the product of the local
factors of `x` over finitely many places, weighted by `mult` at the infinite places, is at most
the height of `x`. -/
theorem prod_apply_le_mulHeight₁ (x : K) :
    (∏ v ∈ Sinf, v x ^ v.mult) * ∏ v ∈ Sfin, v x ≤ mulHeight₁ x := by
  have hinf : ∏ v ∈ Sinf, v x ^ v.mult ≤ ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult :=
    calc ∏ v ∈ Sinf, v x ^ v.mult
      _ ≤ ∏ v ∈ Sinf, max (v x) 1 ^ v.mult := by gcongr; exact le_max_left _ _
      _ ≤ ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult :=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun v _ ↦ by positivity) fun v _ _ ↦ one_le_pow₀ (le_max_right _ _)
  have hfin : ∏ v ∈ Sfin, v x ≤ ∏ᶠ v : FinitePlace K, max (v x) 1 :=
    calc ∏ v ∈ Sfin, v x
      _ ≤ ∏ v ∈ Sfin, max (v x) 1 := by gcongr; exact le_max_left _ _
      _ ≤ ∏ᶠ v : FinitePlace K, max (v x) 1 :=
        Finset.prod_le_finprod_of_one_le₀ Sfin (FinitePlace.hasFiniteMulSupport_max_one x)
          (fun v _ ↦ by positivity) fun v _ ↦ le_max_right _ _
  rw [mulHeight₁_eq]
  exact mul_le_mul hinf hfin (Finset.prod_nonneg fun v _ ↦ by positivity) (by positivity)

/-- **The fundamental inequality, lower bound** (Bombieri–Gubler (1.8)): the product of the local
factors of a nonzero `x` over finitely many places, weighted by `mult` at the infinite places, is
at least the reciprocal of the height of `x`. -/
theorem inv_mulHeight₁_le_prod_apply {x : K} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ (∏ v ∈ Sinf, v x ^ v.mult) * ∏ v ∈ Sfin, v x := by
  have h := prod_apply_le_mulHeight₁ Sinf Sfin x⁻¹
  simp only [map_inv₀, inv_pow, Finset.prod_inv_distrib, ← mul_inv, mulHeight₁_inv] at h
  have hpos : 0 < (∏ v ∈ Sinf, v x ^ v.mult) * ∏ v ∈ Sfin, v x :=
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (InfinitePlace.pos_iff.mpr hx) _)
      (Finset.prod_pos fun v _ ↦ FinitePlace.pos_iff.mpr hx)
  exact (inv_le_comm₀ hpos (mulHeight₁_pos x)).mp h

/-! ### The truncated product -/

/-- The truncated local factors `min 1 |x|_v` of a nonzero `x`, taken over all places and weighted
by `mult` at the infinite places, multiply to the reciprocal of the height of `x`. This is the
product formula read through `min 1 t * max t 1 = t`. -/
theorem prod_min_one_apply_eq_inv_mulHeight₁ {x : K} (hx : x ≠ 0) :
    (∏ v : InfinitePlace K, min 1 (v x) ^ v.mult) * ∏ᶠ v : FinitePlace K, min 1 (v x) =
      (mulHeight₁ x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  calc ((∏ v : InfinitePlace K, min 1 (v x) ^ v.mult) * ∏ᶠ v : FinitePlace K, min 1 (v x)) *
        mulHeight₁ x
      = (∏ v : InfinitePlace K, min 1 (v x) ^ v.mult * max (v x) 1 ^ v.mult) *
          ∏ᶠ v : FinitePlace K, min 1 (v x) * max (v x) 1 := by
        rw [mulHeight₁_eq, Finset.prod_mul_distrib,
          finprod_mul_distrib (FinitePlace.hasFiniteMulSupport_min_one hx)
            (FinitePlace.hasFiniteMulSupport_max_one x)]
        ring
    _ = (∏ v : InfinitePlace K, v x ^ v.mult) * ∏ᶠ v : FinitePlace K, v x := by
        simp_rw [← mul_pow, max_comm _ (1 : ℝ), min_mul_max, one_mul]
    _ = 1 := prod_abs_eq_one hx

/-- **The fundamental inequality in truncated form**: the truncated local factors `min 1 |x|_v`
of a nonzero `x` over finitely many places, weighted by `mult` at the infinite places, multiply to
at least the reciprocal of the height of `x`. -/
theorem inv_mulHeight₁_le_prod_min_one_apply {x : K} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ (∏ v ∈ Sinf, min 1 (v x) ^ v.mult) * ∏ v ∈ Sfin, min 1 (v x) := by
  have h₀ (t : ℝ) (ht : 0 ≤ t) : 0 ≤ min 1 t := le_min zero_le_one ht
  have hinf : ∏ v : InfinitePlace K, min 1 (v x) ^ v.mult ≤ ∏ v ∈ Sinf, min 1 (v x) ^ v.mult :=
    Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.subset_univ _)
      (fun v _ ↦ pow_nonneg (h₀ _ (apply_nonneg _ _)) _)
      fun v _ _ ↦ pow_le_one₀ (h₀ _ (apply_nonneg _ _)) (min_le_left _ _)
  have hfin : ∏ᶠ v : FinitePlace K, min 1 (v x) ≤ ∏ v ∈ Sfin, min 1 (v x) :=
    Finset.finprod_le_prod_of_le_one₀ Sfin (FinitePlace.hasFiniteMulSupport_min_one hx)
      (fun v ↦ h₀ _ (apply_nonneg _ _)) fun v _ ↦ min_le_left _ _
  rw [← prod_min_one_apply_eq_inv_mulHeight₁ hx]
  exact mul_le_mul hinf hfin (finprod_nonneg fun v ↦ h₀ _ (apply_nonneg _ _))
    (Finset.prod_nonneg fun v _ ↦ pow_nonneg (h₀ _ (apply_nonneg _ _)) _)

/-! ### One place at a time -/

/-- The value of `x` at an infinite place is at most the height of `x`: `max |x|_v 1 ≤ H(x)`. -/
theorem InfinitePlace.max_apply_one_le_mulHeight₁ (v : InfinitePlace K) (x : K) :
    max (v x) 1 ≤ mulHeight₁ x := by
  refine max_le ?_ (one_le_mulHeight₁ x)
  have h := prod_apply_le_mulHeight₁ {v} (∅ : Finset (FinitePlace K)) x
  rw [Finset.prod_singleton, Finset.prod_empty, mul_one] at h
  rcases le_or_gt (v x) 1 with h1 | h1
  · exact h1.trans (one_le_mulHeight₁ x)
  · exact (le_self_pow₀ h1.le v.mult_ne_zero).trans h

/-- The value of `x` at a finite place is at most the height of `x`: `max |x|_v 1 ≤ H(x)`. -/
theorem FinitePlace.max_apply_one_le_mulHeight₁ (v : FinitePlace K) (x : K) :
    max (v x) 1 ≤ mulHeight₁ x := by
  refine max_le ?_ (one_le_mulHeight₁ x)
  simpa using prod_apply_le_mulHeight₁ ∅ {v} x

/-- The value of a nonzero `x` at an infinite place is at least the reciprocal of the height of
`x`: `H(x)⁻¹ ≤ min 1 |x|_v`. -/
theorem InfinitePlace.inv_mulHeight₁_le_min_one_apply (v : InfinitePlace K) {x : K}
    (hx : x ≠ 0) : (mulHeight₁ x)⁻¹ ≤ min 1 (v x) := by
  have h := inv_mulHeight₁_le_prod_min_one_apply {v} (∅ : Finset (FinitePlace K)) hx
  rw [Finset.prod_singleton, Finset.prod_empty, mul_one] at h
  exact h.trans (pow_le_of_le_one (le_min zero_le_one (apply_nonneg _ _)) (min_le_left _ _)
    v.mult_ne_zero)

/-- The value of a nonzero `x` at a finite place is at least the reciprocal of the height of
`x`: `H(x)⁻¹ ≤ min 1 |x|_v`. -/
theorem FinitePlace.inv_mulHeight₁_le_min_one_apply (v : FinitePlace K) {x : K} (hx : x ≠ 0) :
    (mulHeight₁ x)⁻¹ ≤ min 1 (v x) := by
  simpa using inv_mulHeight₁_le_prod_min_one_apply ∅ {v} hx

/-! ### Examples -/

/-- At the empty sets of places the upper bound is `Height.one_le_mulHeight₁`. -/
example (x : K) : 1 ≤ mulHeight₁ x := by
  simpa using prod_apply_le_mulHeight₁ (∅ : Finset (InfinitePlace K)) ∅ x

/-- The lower bound fails at `x = 0`: the height of `0` is `1`, while its local factor at any
infinite place vanishes. -/
example (v : InfinitePlace K) :
    ¬(mulHeight₁ (0 : K))⁻¹ ≤ (∏ w ∈ {v}, w (0 : K) ^ w.mult) *
      ∏ w ∈ (∅ : Finset (FinitePlace K)), w (0 : K) := by
  simp

end NumberField
