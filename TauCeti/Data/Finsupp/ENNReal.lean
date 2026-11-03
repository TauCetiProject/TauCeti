/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.Finsupp.Weight

/-!
# Reciprocal natural weights in the extended nonnegative reals

For finitely many coordinates, the weight of `d` with reciprocal natural weights `r` is the
real sum of ratios `∑ i, d i / r i` whenever `d ≤ r`. The bound permits zero weights: their
exponents must also be zero, so they contribute zero to both sums. This identifies extended
nonnegative weights with ordinary real ratios without requiring every weight to be positive.

On a product `κ × ι` of blocks indexed by `κ`, the weight giving the coordinate `(h, i₀ h)` of
each block the reciprocal natural weight `(d h)⁻¹` and every other coordinate the weight `0` is
the sum `∑ h, n (h, i₀ h) / d h`.
-/

public section

namespace Finsupp

open scoped ENNReal

variable {σ : Type*}

/-- If `d ≤ r`, the reciprocal natural weight of `d` in `ℝ≥0∞` is the real sum
`∑ᵢ dᵢ / rᵢ`. Zero weights are allowed, since their corresponding exponents are zero. -/
theorem weight_inv_natCast_eq_ofReal_sum_div [Fintype σ] {r : σ → ℕ}
    {d : σ →₀ ℕ} (hdr : ∀ i, d i ≤ r i) :
    d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) = ENNReal.ofReal (∑ i, (d i : ℝ) / r i) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos (d i) with h | h
  · simp [h]
  · rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 (h.trans_le (hdr i))),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, nsmul_eq_mul, div_eq_mul_inv]

/-- On blocks `κ × ι`, the weight that is `(d h)⁻¹` at the coordinate `(h, i₀ h)` of each block
and `0` elsewhere is the sum `∑ h, n (h, i₀ h) / d h` in `ℝ≥0∞`. -/
theorem weight_ite_inv_natCast_eq_sum_div {κ ι : Type*} [Fintype κ] [Finite ι] [DecidableEq ι]
    (i₀ : κ → ι) (d : κ → ℕ) (n : κ × ι →₀ ℕ) :
    n.weight (fun p ↦ if p.2 = i₀ p.1 then (d p.1 : ℝ≥0∞)⁻¹ else 0) =
      ∑ h, (n (h, i₀ h) : ℝ≥0∞) / d h := by
  have := Fintype.ofFinite ι
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [Fintype.sum_eq_single (i₀ h) fun i hi ↦ by simp [hi]]
  simp [div_eq_mul_inv]

end Finsupp
