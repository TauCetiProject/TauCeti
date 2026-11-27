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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.SpecialFunctions.Sqrt
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
  nonnegative, and bounded by the integral of `|ρ'|`.
* `TauCeti.integral_abs_div_sqrt_pow_le`: if `ψ` is supported in `(a, R)` with `a > 0`, then
  `∫ τ in 0..R², |ψ (√τ) / (√τ) ^ n| ≤ 2 (∫ |ψ|) / a ^ (n - 1)`.
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

/-- A primitive `t ↦ ∫ s in c..t, σ s` of a continuous `σ` vanishing on `(-∞, 0]`, with
`0 ≤ c ≤ d`, is bounded at every `t ≤ c` by `∫ τ in 0..d, |σ τ|`. -/
private lemma abs_integral_le_integral_abs_of_eq_zero {σ : ℝ → ℝ} (hσ : Continuous σ)
    (hσ0 : ∀ τ ≤ 0, σ τ = 0) {c d t : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (ht : t ≤ c) :
    |∫ s in c..t, σ s| ≤ ∫ τ in (0 : ℝ)..d, |σ τ| := by
  have hI : ∀ t, 0 ≤ t → t ≤ c → |∫ s in c..t, σ s| ≤ ∫ τ in (0 : ℝ)..d, |σ τ| := by
    intro t ht0 ht
    calc |∫ s in c..t, σ s| = |∫ τ in t..c, σ τ| := by
          rw [intervalIntegral.integral_symm, abs_neg]
      _ ≤ ∫ τ in t..c, |σ τ| := intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ τ in (0 : ℝ)..d, |σ τ| :=
          intervalIntegral.integral_mono_interval ht0 ht hcd
            (MeasureTheory.ae_of_all _ fun _ ↦ abs_nonneg _) (hσ.abs.intervalIntegrable _ _)
  rcases le_total 0 t with ht0 | ht0
  · exact hI t ht0 ht
  -- Below `0` the primitive is constant, since `σ` vanishes there.
  have h0 : ∫ τ in (0 : ℝ)..t, σ τ = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun τ hτ ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_ge ht0] at hτ
    exact hσ0 τ hτ.2
  rw [← intervalIntegral.integral_add_adjacent_intervals (hσ.intervalIntegrable _ 0)
    (hσ.intervalIntegrable 0 t), h0, add_zero]
  exact hI 0 le_rfl hc

/-- Every test function `ψ` on `(0, R)` is `s ↦ s ^ n ρ' (s ^ 2)` on `(0, ∞)` for a smooth `ρ`
vanishing on `[R' ^ 2, ∞)` for some `R' < R`, and nonpositive when `ψ` is nonnegative: `ρ` is
the primitive of `t ↦ ψ (√t) / (√t) ^ n` vanishing at `R' ^ 2`. It is bounded by the integral
of the absolute value of its derivative over `(0, R ^ 2)`. -/
lemma exists_contDiff_eq_pow_mul_deriv (n : ℕ) (hR : 0 < R) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo 0 R) :
    ∃ R', 0 < R' ∧ R' < R ∧ ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ t, R' ^ 2 ≤ t → ρ t = 0) ∧
      ((∀ s, 0 ≤ ψ s) → ∀ t, ρ t ≤ 0) ∧ (∀ s, 0 < s → ψ s = s ^ n * deriv ρ (s ^ 2)) ∧
      ∀ t, |ρ t| ≤ ∫ τ in (0 : ℝ)..R ^ 2, |ψ (√τ) / (√τ) ^ n| := by
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
    ⟨fun t ↦ (hρderiv t).differentiableAt, hρ' ▸ hσ⟩, hρ0, fun hψn t ↦ ?_, fun s hs ↦ ?_,
    fun t ↦ ?_⟩
  · rcases le_total t (R' ^ 2) with ht | ht
    · simp only [hρ_def]
      rw [intervalIntegral.integral_symm, neg_nonpos]
      exact intervalIntegral.integral_nonneg ht fun s _ ↦
        div_nonneg (hψn _) (pow_nonneg (Real.sqrt_nonneg _) _)
    · exact (hρ0 _ ht).le
  · rw [hρ', hσ_def]
    simp only [Real.sqrt_sq hs.le]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hs.ne')]
  · -- `σ` vanishes on `(-∞, 0]`, and `ρ` vanishes beyond `R' ^ 2`.
    rcases le_total (R' ^ 2) t with ht | ht
    · rw [hρ0 t ht, abs_zero]
      exact intervalIntegral.integral_nonneg (sq_nonneg R) fun _ _ ↦ abs_nonneg _
    exact abs_integral_le_integral_abs_of_eq_zero hσc (fun τ hτ ↦ by
      simp [hσ_def, Real.sqrt_eq_zero'.mpr hτ,
        image_eq_zero_of_notMem_tsupport fun h ↦ lt_irrefl _ (hψs' h).1])
      (sq_nonneg R') (pow_le_pow_left₀ hR'0.le hR'R.le 2) ht

/-- The integral of the radial profile `τ ↦ |ψ (√τ) / (√τ) ^ n|` over `(0, R ^ 2)`, which bounds
the primitive `ρ` of `TauCeti.exists_contDiff_eq_pow_mul_deriv`, is at most
`2 (∫ |ψ|) / a ^ (n - 1)` when `n ≠ 0` and `ψ` is continuous and supported in `(a, R)` with
`a > 0`. -/
lemma integral_abs_div_sqrt_pow_le {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ≠ 0)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψs : tsupport ψ ⊆ Ioo a R) :
    ∫ τ in (0 : ℝ)..R ^ 2, |ψ (√τ) / (√τ) ^ n| ≤ 2 * (∫ s, |ψ s|) / a ^ (n - 1) := by
  rcases lt_or_ge R 0 with hR | hR
  · -- For `R < 0` the support of `ψ` is empty.
    have hψ0 (s : ℝ) : ψ s = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ by
      linarith [(hψs h).1, (hψs h).2]
    simp [hψ0]
  set g : ℝ → ℝ := fun τ ↦ |ψ (√τ) / (√τ) ^ n| with hg_def
  have hg : Continuous g := (Real.contDiff_div_sqrt_pow (contDiff_zero.2 hψ)
    (hψs.trans fun s hs ↦ ha.trans hs.1) n).continuous.abs
  have han : 0 < a ^ (n - 1) := pow_pos ha _
  -- Substitute `τ = s ^ 2`.
  have hsub : ∫ τ in (0 : ℝ)..R ^ 2, g τ = ∫ s in (0 : ℝ)..R, g (s ^ 2) * (2 * s) := by
    have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := R) (f := fun s ↦ s ^ 2)
      (f' := fun s ↦ 2 * s) (g := g) (fun s _ ↦ by simpa using hasDerivAt_pow 2 s)
      (by fun_prop) hg
    simpa using h.symm
  have hpt : ∀ s ∈ Icc (0 : ℝ) R, g (s ^ 2) * (2 * s) ≤ 2 * |ψ s| / a ^ (n - 1) := by
    intro s hs
    rw [hg_def]
    simp only [Real.sqrt_sq hs.1]
    by_cases hψ0 : ψ s = 0
    · simp only [hψ0, zero_div, abs_zero, zero_mul, mul_zero]
      exact le_refl _
    have hs0 : a < s := (hψs (subset_tsupport _ hψ0)).1
    have hspos : 0 < s := ha.trans hs0
    have hpow : s ^ n = s ^ (n - 1) * s := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)]
    rw [abs_div, abs_of_pos (pow_pos hspos n), hpow]
    calc |ψ s| / (s ^ (n - 1) * s) * (2 * s) = 2 * |ψ s| / s ^ (n - 1) := by
          field_simp
      _ ≤ 2 * |ψ s| / a ^ (n - 1) :=
          div_le_div_of_nonneg_left (by positivity) han (pow_le_pow_left₀ ha.le hs0.le _)
  have hsupp : Function.support (fun s ↦ |ψ s|) ⊆ Ioc 0 R := fun s hs ↦ by
    have h := hψs (subset_tsupport _ (by simpa using hs))
    exact ⟨ha.trans h.1, h.2.le⟩
  calc ∫ τ in (0 : ℝ)..R ^ 2, g τ = ∫ s in (0 : ℝ)..R, g (s ^ 2) * (2 * s) := hsub
    _ ≤ ∫ s in (0 : ℝ)..R, 2 * |ψ s| / a ^ (n - 1) :=
        intervalIntegral.integral_mono_on hR
          ((by fun_prop : Continuous fun s ↦ g (s ^ 2) * (2 * s)).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun s ↦ 2 * |ψ s| / a ^ (n - 1)).intervalIntegrable _ _)
          hpt
    _ = 2 * (∫ s, |ψ s|) / a ^ (n - 1) := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_eq_integral_of_support_subset hsupp]

end TauCeti
