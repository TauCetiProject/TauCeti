/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# The absorption lemma for estimates between nested radii

Let `f` be bounded above on an interval `[r₀, r₁]` and satisfy

`f s ≤ θ f t + A (t - s)^{-β} + B` whenever `r₀ ≤ s < t ≤ r₁`,

with `0 ≤ θ < 1` and `A, B ≥ 0`. Then `f r₀ ≤ C (A (r₁ - r₀)^{-β} + B)`, where `C` depends only
on `θ` and `β`. The term `θ f t` is *absorbed*: iterating the inequality along the radii
`sᵢ = r₁ - τⁱ (r₁ - r₀)`, for a ratio `τ ∈ (0, 1)` with `θ < τ^β`, produces a convergent
geometric series, while the bounded remainder `θᵏ f(sₖ)` tends to zero.

This is the standard device for removing a fraction of the quantity being estimated from the
right-hand side of an estimate on concentric balls, where `f r` is a norm of the unknown on the
ball of radius `r`. In De Giorgi–Nash–Moser theory it turns an `L²` bound for the supremum of a
subsolution into an `Lᵖ` bound with `p < 2`.

## Main declarations

* `TauCeti.exists_le_mul_mul_rpow_add_of_le_mul_add`: the absorption lemma.

## References

* M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic
  Systems*, Chapter V, Lemma 3.1.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Lemma 4.3.
-/

public section

namespace TauCeti

open Filter Set Topology

/-- **The absorption lemma.** Fix `0 ≤ θ < 1` and an exponent `β`. There is `C > 0`, depending
only on `θ` and `β`, such that the following holds. Let `f` be bounded above on `[r₀, r₁]`,
with `r₀ < r₁`, and suppose that

`f s ≤ θ f t + A (t - s)^{-β} + B` whenever `r₀ ≤ s < t ≤ r₁`,

for some `A, B ≥ 0`. Then `f r₀ ≤ C (A (r₁ - r₀)^{-β} + B)`. -/
theorem exists_le_mul_mul_rpow_add_of_le_mul_add {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (β : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {f : ℝ → ℝ} {r₀ r₁ A B : ℝ}, r₀ < r₁ → 0 ≤ A → 0 ≤ B →
      BddAbove (f '' Icc r₀ r₁) →
      (∀ s t, r₀ ≤ s → s < t → t ≤ r₁ → f s ≤ θ * f t + A * (t - s) ^ (-β) + B) →
      f r₀ ≤ C * (A * (r₁ - r₀) ^ (-β) + B) := by
  obtain ⟨τ, hτ0, hτ1, hθτ⟩ := Real.exists_pos_lt_one_lt_rpow hθ1 β
  -- The ratio of the geometric series produced by the `A`-terms.
  set q := θ * τ ^ (-β)
  have hq0 : 0 ≤ q := mul_nonneg hθ0 (Real.rpow_nonneg hτ0.le _)
  have hq1 : θ * τ ^ (-β) < 1 := by
    rw [Real.rpow_neg hτ0.le, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hτ0 β)]
    exact hθτ
  have hθ' : 0 < 1 - θ := sub_pos.2 hθ1
  have hq' : 0 < 1 - q := sub_pos.2 hq1
  refine ⟨max ((1 - τ) ^ (-β) / (1 - q)) (1 - θ)⁻¹, lt_max_of_lt_right (inv_pos.2 hθ'), ?_⟩
  intro f r₀ r₁ A B hr hA hB hbdd hf
  obtain ⟨M, hM⟩ := hbdd
  set d := r₁ - r₀
  have hd : 0 < d := sub_pos.2 hr
  -- The radii `sᵢ = r₁ - τⁱ d` increase from `s₀ = r₀` towards `r₁`.
  set s : ℕ → ℝ := fun i => r₁ - τ ^ i * d
  have hs_mem : ∀ i, s i ∈ Icc r₀ r₁ := fun i => by
    have h1 : τ ^ i ≤ 1 := pow_le_one₀ hτ0.le hτ1.le
    have h0 : 0 ≤ τ ^ i * d := by positivity
    constructor <;> nlinarith
  have hgap : ∀ i, s (i + 1) - s i = τ ^ i * ((1 - τ) * d) := fun i => by
    simp only [s, pow_succ]
    ring
  set K := ((1 - τ) * d) ^ (-β)
  have hK : 0 ≤ K := Real.rpow_nonneg (by nlinarith) _
  have hgapβ : ∀ i, (s (i + 1) - s i) ^ (-β) = (τ ^ (-β)) ^ i * K := fun i => by
    rw [hgap, Real.mul_rpow (pow_nonneg hτ0.le i) (by nlinarith),
      Real.rpow_pow_comm hτ0.le]
  -- Iterating `k` times leaves `θᵏ f(sₖ)` and a partial geometric sum.
  have key : ∀ k : ℕ, f r₀ ≤ θ ^ k * f (s k) +
      ∑ i ∈ Finset.range k, (A * K * q ^ i + B * θ ^ i) := by
    intro k
    induction k with
    | zero => simp [s, d]
    | succ k ih =>
      have hlt : s k < s (k + 1) := by
        have := mul_pos (pow_pos hτ0 k) (mul_pos (sub_pos.2 hτ1) hd)
        linarith [hgap k]
      have hstep := hf (s k) (s (k + 1)) (hs_mem k).1 hlt (hs_mem (k + 1)).2
      rw [hgapβ] at hstep
      have hθk : 0 ≤ θ ^ k := pow_nonneg hθ0 k
      have := mul_le_mul_of_nonneg_left hstep hθk
      rw [Finset.sum_range_succ, mul_pow]
      calc f r₀ ≤ θ ^ k * f (s k) + ∑ i ∈ Finset.range k, (A * K * q ^ i + B * θ ^ i) := ih
        _ ≤ θ ^ k * (θ * f (s (k + 1)) + A * ((τ ^ (-β)) ^ k * K) + B) +
            ∑ i ∈ Finset.range k, (A * K * q ^ i + B * θ ^ i) := by gcongr
        _ = _ := by rw [pow_succ]; ring
  -- The partial sums are bounded by the full geometric series.
  have hsum : ∀ k : ℕ, ∑ i ∈ Finset.range k, (A * K * q ^ i + B * θ ^ i) ≤
      A * K / (1 - q) + B / (1 - θ) := fun k => by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, div_eq_mul_inv,
      div_eq_mul_inv]
    have hgq := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hq0 hq1
    have hgθ := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hθ0 hθ1
    rw [pow_zero, one_div, ← Finset.range_eq_Ico] at hgq hgθ
    gcongr
  have hbound : ∀ k : ℕ, f r₀ ≤ θ ^ k * max M 0 + (A * K / (1 - q) + B / (1 - θ)) := fun k =>
    (key k).trans (add_le_add (mul_le_mul_of_nonneg_left
      ((hM (mem_image_of_mem f (hs_mem k))).trans (le_max_left _ _)) (pow_nonneg hθ0 k))
      (hsum k))
  have hlim : Tendsto (fun k : ℕ => θ ^ k * max M 0 + (A * K / (1 - q) + B / (1 - θ))) atTop
      (𝓝 (A * K / (1 - q) + B / (1 - θ))) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const (max M 0)).add_const
      (A * K / (1 - q) + B / (1 - θ))
  refine (ge_of_tendsto' hlim hbound).trans ?_
  -- Compare with the constant `C`.
  have hKd : K = (1 - τ) ^ (-β) * d ^ (-β) := Real.mul_rpow (by linarith) hd.le
  have hdβ : 0 ≤ d ^ (-β) := Real.rpow_nonneg hd.le _
  rw [hKd, mul_add]
  gcongr ?_ + ?_
  · calc A * ((1 - τ) ^ (-β) * d ^ (-β)) / (1 - q)
          = A * d ^ (-β) * ((1 - τ) ^ (-β) / (1 - q)) := by ring
      _ ≤ A * d ^ (-β) * max ((1 - τ) ^ (-β) / (1 - q)) (1 - θ)⁻¹ := by
          gcongr
          exact le_max_left _ _
      _ = _ := by ring
  · rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hB

end TauCeti
