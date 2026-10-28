/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# The norm of an element with the same absolute value at every infinite place

Mathlib's `NumberField.InfinitePlace.prod_eq_abs_norm` writes the absolute value of the norm
`N_{K/ℚ}(x)` as the product `∏_w w(x) ^ m_w` over the infinite places of `K`, where the
multiplicities `m_w` add up to `[K : ℚ]` (`NumberField.InfinitePlace.sum_mult_eq`). If `x` has the
same absolute value `r` at every infinite place, the product is therefore `r ^ [K : ℚ]`.

This is how the absolute value of a Gauss or Jacobi sum, which is the same under every complex
embedding, determines its norm, and with it the norm of the principal ideal it generates.

## Main results

* `NumberField.InfinitePlace.abs_norm_eq_pow_finrank`: if `w x = r` for every infinite place `w`,
  then `|N_{K/ℚ}(x)| = r ^ [K : ℚ]`.
-/

public section

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- **The norm of an element of constant absolute value.** If `x` has absolute value `r` at every
infinite place of the number field `K`, then `|N_{K/ℚ}(x)| = r ^ [K : ℚ]`. By
`NumberField.InfinitePlace.eq_iff_eq` the hypothesis says that `‖σ x‖ = r` for every complex
embedding `σ` of `K`. -/
theorem abs_norm_eq_pow_finrank {x : K} {r : ℝ} (h : ∀ w : InfinitePlace K, w x = r) :
    |(Algebra.norm ℚ x : ℝ)| = r ^ Module.finrank ℚ K := by
  rw [← Rat.cast_abs, ← prod_eq_abs_norm]
  simp_rw [h]
  rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq]

end NumberField.InfinitePlace
