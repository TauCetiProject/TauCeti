/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.Topology.Instances.Real.TSupport

/-!
# Radial test functions as derivatives of weighted primitives

Computations behind radial test functions on `ℝⁿ`: the radial Laplacian weight of
`s ↦ ρ (s ^ 2)` is twice the derivative of `s ↦ s ^ n ρ' (s ^ 2)`, and every smooth test
function `ψ` supported in `(0, R)` is of the form `s ↦ s ^ n ρ' (s ^ 2)` for a smooth `ρ`.

## Main results

* `TauCeti.pow_mul_add_eq_two_mul_deriv`: if `ψ r = r ^ n * σ (r ^ 2)` for `r > 0`, then
  `s ^ (n - 1) (4 s² σ' (s²) + 2 n σ (s²)) = 2 ψ' s` at `s > 0`.
* `TauCeti.exists_contDiff_eq_pow_mul_deriv`: every smooth `ψ` supported in `(0, R)` is
  `s ↦ s ^ n ρ' (s ^ 2)` for a smooth `ρ` vanishing for large arguments, nonpositive when `ψ` is
  nonnegative.
-/

public section

namespace TauCeti

open Filter Set Topology
open scoped ContDiff

variable {R : ℝ}

/-- If `ψ r = r ^ n * σ (r ^ 2)` for `r > 0`, then at `s > 0` the radial Laplacian weight
`s ^ (n - 1) (4 s² σ' (s²) + 2 n σ (s²))` is `2 ψ' s`. -/
lemma pow_mul_add_eq_two_mul_deriv {n : ℕ} (hn : n ≠ 0) {σ ψ : ℝ → ℝ} {s : ℝ}
    (hσ : DifferentiableAt ℝ σ (s ^ 2)) (hψ : ∀ r, 0 < r → ψ r = r ^ n * σ (r ^ 2))
    (hs : 0 < s) :
    s ^ (n - 1) * (4 * s ^ 2 * deriv σ (s ^ 2) + 2 * (n : ℝ) * σ (s ^ 2)) = 2 * deriv ψ s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  have hψeq : ψ =ᶠ[𝓝 s] fun r ↦ r ^ (m + 1) * σ (r ^ 2) :=
    eventually_of_mem (Ioi_mem_nhds hs) hψ
  have hd : HasDerivAt (fun r ↦ r ^ (m + 1) * σ (r ^ 2))
      (((m + 1 : ℕ) : ℝ) * s ^ (m + 1 - 1) * σ (s ^ 2) +
        s ^ (m + 1) * (deriv σ (s ^ 2) * ((2 : ℕ) * s ^ (2 - 1)))) s :=
    (hasDerivAt_pow _ s).mul
      ((hσ.hasDerivAt : HasDerivAt σ (deriv σ (s ^ 2)) (s ^ 2)).comp
        (h := fun x : ℝ ↦ x ^ 2) s (hasDerivAt_pow 2 s))
  rw [hψeq.deriv_eq, hd.deriv]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

/-- Every test function `ψ` on `(0, R)` is `s ↦ s ^ n ρ' (s ^ 2)` on `(0, ∞)` for a smooth `ρ`
vanishing on `[R' ^ 2, ∞)` for some `R' < R`, and nonpositive when `ψ` is nonnegative: `ρ` is
the primitive of `t ↦ ψ (√t) / (√t) ^ n` vanishing at `R' ^ 2`. -/
lemma exists_contDiff_eq_pow_mul_deriv (n : ℕ) (hR : 0 < R) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo 0 R) :
    ∃ R', 0 < R' ∧ R' < R ∧ ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ t, R' ^ 2 ≤ t → ρ t = 0) ∧
      ((∀ s, 0 ≤ ψ s) → ∀ t, ρ t ≤ 0) ∧ ∀ s, 0 < s → ψ s = s ^ n * deriv ρ (s ^ 2) := by
  obtain ⟨R', hR'0, hR'R, hψs'⟩ := exists_lt_tsupport_subset_Ioo hR hψs
  set σ : ℝ → ℝ := fun t ↦ ψ (√t) / (√t) ^ n with hσ_def
  have hσ0 : ∀ t, R' ^ 2 ≤ t → σ t = 0 := by
    intro t ht
    have : R' ≤ √t := by
      rw [← Real.sqrt_sq hR'0.le]
      exact Real.sqrt_le_sqrt ht
    simp [hσ_def, image_eq_zero_of_notMem_tsupport fun h ↦ (hψs' h).2.not_ge this]
  have hσ : ContDiff ℝ ∞ σ := Real.contDiff_div_sqrt_pow hψ (hψs'.trans Ioo_subset_Ioi_self) n
  have hσc : Continuous σ := hσ.continuous
  set ρ : ℝ → ℝ := fun t ↦ ∫ s in R' ^ 2..t, σ s with hρ_def
  have hρderiv : ∀ t, HasDerivAt ρ (σ t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (hσc.intervalIntegrable _ _)
      (hσc.stronglyMeasurableAtFilter _ _) hσc.continuousAt
  have hρ' : deriv ρ = σ := funext fun t ↦ (hρderiv t).deriv
  have hρ0 : ∀ t, R' ^ 2 ≤ t → ρ t = 0 := by
    intro t ht
    simp only [hρ_def]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_le ht] at hs
    exact hσ0 s hs.1
  refine ⟨R', hR'0, hR'R, ρ, contDiff_infty_iff_deriv.mpr
    ⟨fun t ↦ (hρderiv t).differentiableAt, hρ' ▸ hσ⟩, hρ0, fun hψn t ↦ ?_, fun s hs ↦ ?_⟩
  · rcases le_total t (R' ^ 2) with ht | ht
    · simp only [hρ_def]
      rw [intervalIntegral.integral_symm, neg_nonpos]
      exact intervalIntegral.integral_nonneg ht fun s _ ↦
        div_nonneg (hψn _) (pow_nonneg (Real.sqrt_nonneg _) _)
    · exact (hρ0 _ ht).le
  · rw [hρ', hσ_def]
    simp only [Real.sqrt_sq hs.le]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hs.ne')]

end TauCeti
