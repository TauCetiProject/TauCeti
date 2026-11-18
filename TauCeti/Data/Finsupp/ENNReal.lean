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
the sum `∑ h, n (h, i₀ h) / d h`. More generally, for finitely many coordinates the reciprocal
natural weight of `m` is `∑ i, (m i : ℝ≥0∞) / r i` (`Finsupp.weight_inv_natCast_eq_sum_div`), and
taking infima over a projected family matches the infimum of reciprocal weights on the image
(`Finsupp.iInf_sum_div_eq_iInf_weight`).
-/

public section

namespace Finsupp

open scoped ENNReal

variable {σ : Type*}

/-- For finitely many coordinates, the reciprocal natural weight of `m` in `ℝ≥0∞` is the sum
`∑ i, (m i : ℝ≥0∞) / r i`. -/
theorem weight_inv_natCast_eq_sum_div [Fintype σ] (r : σ → ℕ) (m : σ →₀ ℕ) :
    m.weight (fun i ↦ (r i : ℝ≥0∞)⁻¹) = ∑ i, (m i : ℝ≥0∞) / r i := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [nsmul_eq_mul, div_eq_mul_inv]

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
theorem weight_ite_inv_natCast_eq_sum_div {κ ι : Type*} [Fintype κ] [DecidableEq ι]
    (i₀ : κ → ι) (d : κ → ℕ) (n : κ × ι →₀ ℕ) :
    n.weight (fun p ↦ if p.2 = i₀ p.1 then (d p.1 : ℝ≥0∞)⁻¹ else 0) =
      ∑ h, (n (h, i₀ h) : ℝ≥0∞) / d h := by
  classical
  have hinj : Function.Injective fun h ↦ (h, i₀ h) := fun _ _ h ↦ (Prod.ext_iff.1 h).1
  rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset n Finset.subset_union_left _ (by simp),
    ← Finset.sum_subset (s₁ := Finset.univ.image fun h ↦ (h, i₀ h)) Finset.subset_union_right
      fun p _ hp ↦ ?_, Finset.sum_image fun _ _ _ _ h ↦ hinj h]
  · simp [div_eq_mul_inv]
  · have : p.2 ≠ i₀ p.1 := fun h ↦ hp (Finset.mem_image.2 ⟨p.1, Finset.mem_univ _, by simp [← h]⟩)
    simp [this]

/-- An infimum of reciprocal-weighted sums `∑ h, (π n h : ℝ≥0∞) / d h` over `n` satisfying `p`
equals the infimum of `Finsupp.weight (fun h ↦ (d h : ℝ≥0∞)⁻¹) m` over `m : κ →₀ ℕ` satisfying `q`,
whenever `q` characterizes the `π`-projections of elements satisfying `p`. -/
theorem iInf_sum_div_eq_iInf_weight {α κ : Type*} [Fintype κ]
    (d : κ → ℕ) {p : α → Prop} {q : (κ →₀ ℕ) → Prop} {π : α → κ → ℕ}
    (hq : ∀ m, q m ↔ ∃ n, p n ∧ ∀ h, π n h = m h) :
    (⨅ (n) (_ : p n), ∑ h, (π n h : ℝ≥0∞) / d h) =
      ⨅ (m) (_ : q m), m.weight (fun h ↦ (d h : ℝ≥0∞)⁻¹) := by
  refine le_antisymm (le_iInf₂ fun m hm ↦ ?_) (le_iInf₂ fun n hn ↦ ?_)
  · obtain ⟨n, hn, hmn⟩ := (hq m).mp hm
    refine (iInf₂_le n hn).trans_eq ?_
    rw [weight_inv_natCast_eq_sum_div]
    exact Finset.sum_congr rfl fun h _ ↦ by rw [hmn h]
  · let m : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm (π n)
    have hm : q m := (hq m).mpr ⟨n, hn, fun h ↦ by simp [m]⟩
    refine (iInf₂_le m hm).trans_eq ?_
    rw [weight_inv_natCast_eq_sum_div]
    exact Finset.sum_congr rfl fun h _ ↦ by simp [m]

end Finsupp
