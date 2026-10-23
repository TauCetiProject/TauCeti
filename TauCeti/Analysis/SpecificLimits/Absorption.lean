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
* `TauCeti.sq_mul_le_of_forall_le`: a coupled form for two quantities `k` and `h` on concentric
  balls, where `k` is bounded by `h` and `h` by an arbitrarily small multiple of `k`. It absorbs
  the weighted suprema `sup (R - σ) h(σ)` and `sup (R - σ)² k(σ)`, as in the interior `W^{2,p}`
  estimate.

## References

* M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic
  Systems*, Chapter V, Lemma 3.1.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Lemma 4.3.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, proof of
  Theorem 9.11 (the weighted interior seminorms).
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

/-- The arithmetic of the absorption. If `θ (16 K c_A + 4 c_B + 1) = 1` and the weighted
suprema satisfy `Φ₂ ≤ P + 4 K c_A (Φ₁ + z)` and
`Φ₁ ≤ 2 θ Φ₂ + 2 θ c_B Φ₁ + (2 θ c_B + 2 N / θ) z`, then `Φ₁` can be absorbed and `Φ₂` is bounded
by `P` and `z` alone. -/
private theorem le_two_mul_add_mul_sq_mul_of_le_of_le {Φ₁ Φ₂ P z K cA cB N θ : ℝ}
    (hΦ₁0 : 0 ≤ Φ₁) (hz0 : 0 ≤ z) (hP0 : 0 ≤ P) (hK1 : 1 ≤ K) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hN : 0 ≤ N) (hθ0 : 0 < θ) (hθ : θ * (16 * K * cA + 4 * cB + 1) = 1)
    (hΦ₂ : Φ₂ ≤ P + 4 * K * cA * (Φ₁ + z))
    (hΦ₁ : Φ₁ ≤ 2 * θ * Φ₂ + 2 * θ * cB * Φ₁ + (2 * θ * cB + 2 * N / θ) * z) :
    Φ₂ ≤ 2 * P + (8 * cA + 256 * cA ^ 2 * N + 16 * cA * N * (4 * cB + 1)) * K ^ 2 * z := by
  have hNθ : N / θ = N * (16 * K * cA + 4 * cB + 1) := by
    rw [div_eq_iff hθ0.ne']
    linear_combination (-N) * hθ
  have hα : θ * (16 * K * cA + 4 * cB) ≤ 1 := by nlinarith
  have h2θ : 2 * θ * Φ₂ ≤ 2 * θ * (P + 4 * K * cA * (Φ₁ + z)) :=
    mul_le_mul_of_nonneg_left hΦ₂ (by positivity)
  have hαΦ := mul_le_mul_of_nonneg_right hα hΦ₁0
  have hαz := mul_le_mul_of_nonneg_right hα hz0
  have hΦ₁' : Φ₁ ≤ 4 * θ * P + z + 4 * (N / θ) * z := by
    rw [mul_div_assoc] at hΦ₁
    linarith
  rw [hNθ] at hΦ₁'
  have h16 : 16 * K * cA * θ ≤ 1 := by nlinarith
  have hKK : K ≤ K ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left hΦ₁' (by positivity : (0 : ℝ) ≤ 4 * K * cA)
  have h5 := mul_le_mul_of_nonneg_right h16 hP0
  have h6 := mul_le_mul_of_nonneg_right hKK
    (by positivity : (0 : ℝ) ≤ (8 * cA + 16 * cA * N * (4 * cB + 1)) * z)
  nlinarith

/-- **Absorption over concentric balls.** Let `0 < r < R`, and let `k`, `h`, `y` be nonnegative
functions of the radius, thought of as the norms of `D²u`, `∇u` and `u` on `B_σ`, with `k` and
`h` bounded on `(0, R)` by their values at `R` and `y ≤ z` there. Suppose that for `0 < s < t ≤ R`

`k(s) ≤ a₀ + K (c_A (t - s)⁻¹ h(t) + c_A (t - s)⁻² z)` and
`h(s) ≤ η (k(t) + c_B (t - s)⁻¹ h(t) + c_B (t - s)⁻² y(t)) + (N / η) y(t)` for all `η > 0`.

Then `(R - r)² k(r)` is bounded by `R² a₀` and `z` alone. The proof absorbs the weighted suprema
`sup (R - σ) h(σ)` and `sup (R - σ)² k(σ)` over `0 < σ < R`, applying both inequalities at `σ` and
the midpoint `(σ + R) / 2`. -/
theorem sq_mul_le_of_forall_le {R z a₀ K cA cB N : ℝ} {k h y : ℝ → ℝ} (hR0 : 0 < R)
    (hz0 : 0 ≤ z) (ha₀ : 0 ≤ a₀) (hK1 : 1 ≤ K) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) (hN : 0 ≤ N)
    (hk0 : ∀ σ, 0 ≤ k σ) (hh0 : ∀ σ, 0 ≤ h σ) (hkR : ∀ σ ∈ Set.Ioo 0 R, k σ ≤ k R)
    (hhR : ∀ σ ∈ Set.Ioo 0 R, h σ ≤ h R) (hyz : ∀ σ ∈ Set.Ioo 0 R, y σ ≤ z)
    (hA : ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R →
      k s ≤ a₀ + K * (cA / (t - s) * h t + cA / (t - s) ^ 2 * z))
    (hB : ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R → ∀ {η : ℝ}, 0 < η →
      h s ≤ η * (k t + cB / (t - s) * h t + cB / (t - s) ^ 2 * y t) + N / η * y t)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    (R - r) ^ 2 * k r ≤
      2 * (R ^ 2 * a₀) + (8 * cA + 256 * cA ^ 2 * N + 16 * cA * N * (4 * cB + 1)) * K ^ 2 * z := by
  -- The weighted suprema `Φ₁ = sup (R - σ) h(σ)` and `Φ₂ = sup (R - σ)² k(σ)` over `0 < σ < R`.
  set I := Set.Ioo (0 : ℝ) R
  have hI : R / 2 ∈ I := ⟨by positivity, by linarith⟩
  have hbdd₁ : BddAbove ((fun σ => (R - σ) * h σ) '' I) := ⟨R * h R, by
    rintro _ ⟨σ, hσ, rfl⟩
    exact mul_le_mul (by linarith [hσ.1]) (hhR σ hσ) (hh0 σ) hR0.le⟩
  have hbdd₂ : BddAbove ((fun σ => (R - σ) ^ 2 * k σ) '' I) := ⟨R ^ 2 * k R, by
    rintro _ ⟨σ, hσ, rfl⟩
    exact mul_le_mul (pow_le_pow_left₀ (by linarith [hσ.2]) (by linarith [hσ.1]) 2)
      (hkR σ hσ) (hk0 σ) (by positivity)⟩
  set Φ₁ := sSup ((fun σ => (R - σ) * h σ) '' I)
  set Φ₂ := sSup ((fun σ => (R - σ) ^ 2 * k σ) '' I)
  have hle₁ : ∀ σ ∈ I, (R - σ) * h σ ≤ Φ₁ := fun σ hσ => le_csSup hbdd₁ ⟨σ, hσ, rfl⟩
  have hle₂ : ∀ σ ∈ I, (R - σ) ^ 2 * k σ ≤ Φ₂ := fun σ hσ => le_csSup hbdd₂ ⟨σ, hσ, rfl⟩
  have hΦ₁0 : 0 ≤ Φ₁ := (mul_nonneg (by linarith) (hh0 _)).trans (hle₁ _ hI)
  have hmid : ∀ σ ∈ I, (σ + R) / 2 ∈ I ∧ σ < (σ + R) / 2 := fun σ hσ =>
    ⟨⟨by linarith [hσ.1], by linarith [hσ.2]⟩, by linarith [hσ.2]⟩
  -- Step (A) at `σ` and the midpoint `σ' = (σ + R) / 2` bounds `Φ₂` by `Φ₁`.
  have hΦ₂ : Φ₂ ≤ R ^ 2 * a₀ + 4 * K * cA * (Φ₁ + z) := by
    refine csSup_le ⟨_, Set.mem_image_of_mem _ hI⟩ ?_
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨hσ', hσσ'⟩ := hmid σ hσ
    set d := (R - σ) / 2 with hd
    have hd0 : 0 < d := by linarith [hσ.2]
    have hstep := hA hσ.1 hσσ' hσ'.2.le
    have h1 := hle₁ _ hσ'
    rw [show (σ + R) / 2 - σ = d by rw [hd]; ring] at hstep
    rw [show R - (σ + R) / 2 = d by rw [hd]; ring] at h1
    have hRσ : R - σ = 2 * d := by rw [hd]; ring
    calc (R - σ) ^ 2 * k σ
        ≤ (R - σ) ^ 2 * (a₀ + K * (cA / d * h ((σ + R) / 2) + cA / d ^ 2 * z)) :=
          mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
      _ = (R - σ) ^ 2 * a₀ + 4 * K * cA * (d * h ((σ + R) / 2)) +
            4 * K * cA * z := by
          rw [hRσ]
          field_simp
          ring
      _ ≤ R ^ 2 * a₀ + 4 * K * cA * Φ₁ + 4 * K * cA * z := by
          gcongr
          · linarith [hσ.2]
          · linarith [hσ.1]
      _ = _ := by ring
  -- Step (B) with `η = θ (R - σ) / 2` bounds `Φ₁` by a small multiple of `Φ₂` and of itself.
  set θ := 1 / (16 * K * cA + 4 * cB + 1) with hθ
  have hθ0 : 0 < θ := by positivity
  have hΦ₁ : Φ₁ ≤ 2 * θ * Φ₂ + 2 * θ * cB * Φ₁ + (2 * θ * cB + 2 * N / θ) * z := by
    refine csSup_le ⟨_, Set.mem_image_of_mem _ hI⟩ ?_
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨hσ', hσσ'⟩ := hmid σ hσ
    set d := (R - σ) / 2 with hd
    have hd0 : 0 < d := by linarith [hσ.2]
    have hstep := hB hσ.1 hσσ' hσ'.2.le (η := θ * d) (by positivity)
    have h1 := hle₁ _ hσ'
    have h2 := hle₂ _ hσ'
    rw [show (σ + R) / 2 - σ = d by rw [hd]; ring] at hstep
    rw [show R - (σ + R) / 2 = d by rw [hd]; ring] at h1 h2
    have hyz' : y ((σ + R) / 2) ≤ z := hyz _ hσ'
    have hRσ : R - σ = 2 * d := by rw [hd]; ring
    calc (R - σ) * h σ
        ≤ (R - σ) * (θ * d * (k ((σ + R) / 2) + cB / d * h ((σ + R) / 2) +
            cB / d ^ 2 * y ((σ + R) / 2)) + N / (θ * d) * y ((σ + R) / 2)) :=
          mul_le_mul_of_nonneg_left hstep (by linarith [hσ.2])
      _ = 2 * θ * (d ^ 2 * k ((σ + R) / 2)) + 2 * θ * cB * (d * h ((σ + R) / 2)) +
            (2 * θ * cB + 2 * N / θ) * y ((σ + R) / 2) := by
          rw [hRσ]
          field_simp
          ring
      _ ≤ _ := by gcongr
  -- Absorbing `Φ₁`, then bounding `Φ₂`.
  have hθeq : θ * (16 * K * cA + 4 * cB + 1) = 1 := by
    rw [hθ]
    exact one_div_mul_cancel (by positivity)
  exact (hle₂ r ⟨hr, hrR⟩).trans
    (le_two_mul_add_mul_sq_mul_of_le_of_le hΦ₁0 hz0 (by positivity) hK1 hcA hcB hN hθ0 hθeq hΦ₂ hΦ₁)

end TauCeti
