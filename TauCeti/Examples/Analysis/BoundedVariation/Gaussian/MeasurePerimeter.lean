/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Probability.Distributions.Gaussian.IntegrationByParts.Basic
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# The perimeter against the Gaussian measure is not the Gaussian perimeter

The plausible wrong definition of the Gaussian perimeter, the supremum of `∫_U div X dγ` over test
vector fields with `‖X‖ ≤ 1` and without the term `−⟨x, X⟩` of the Gaussian divergence, is Tau
Ceti's `TauCeti.perimeter γ Ω U` with the measure `γ` in place of `volume`. On the line it assigns
to the whole space `ℝ` the value `√(2/π) ≈ 0.7979` instead of `0`: Gaussian integration by
parts (`TauCeti.Probability.integral_mul_eq_integral_deriv_gaussianReal`) turns `∫ X' dγ` into
`∫ t X(t) dγ`, which is at most `∫ |t| dγ`, and test fields approximating the sign function
attain it. As the empty set has perimeter `0` for every measure, this perimeter is not complement
invariant, unlike the Gaussian perimeter (`TauCeti.gaussianPerimeter_univ`).
-/

open Filter MeasureTheory ProbabilityTheory Set TestFunction TopologicalSpace
open scoped Topology ENNReal Distributions

public noncomputable section

namespace TauCeti.Examples.GaussianMeasurePerimeter

/-- **Gaussian integration by parts** for a test field on `ℝ`: `∫ X' dγ = ∫ t X(t) dγ`. -/
private theorem integral_divergenceCLM_gaussianReal (X : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ∫ x, divergenceCLM X x ∂gaussianReal 0 1 = ∫ x, x * X x ∂gaussianReal 0 1 := by
  simp_rw [divergenceCLM_apply_eq_deriv]
  exact (Probability.integral_mul_eq_integral_deriv_gaussianReal X
    (X.contDiff.differentiable (by simp))
    ((continuous_id.mul X.continuous).integrable_of_hasCompactSupport X.hasCompactSupport.mul_left)
    ((X.contDiff.continuous_deriv (by simp)).integrable_of_hasCompactSupport
      X.hasCompactSupport.deriv)).symm

/-- The perimeter of `ℝ` against `γ` is the supremum of `∫ t X(t) dγ` over test fields. -/
private theorem perimeter_gaussianReal_univ_eq_iSup :
    perimeter (gaussianReal 0 1) ⊤ univ = ⨆ (X : 𝓓((⊤ : Opens ℝ), ℝ)) (_ : ∀ x, ‖X x‖ ≤ 1),
      ENNReal.ofReal (∫ x, x * X x ∂gaussianReal 0 1) := by
  rw [perimeter_eq_iSup nullMeasurableSet_univ]
  simp_rw [setIntegral_univ, integral_divergenceCLM_gaussianReal]

/-- A positive real lies in `[1/(n+1), n + 2 − 1/(n+1)]` for all large `n`. -/
private theorem eventually_mem_Icc_one_div {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, s ∈ Icc (0 + 1 / ((n : ℝ) + 1)) ((n : ℝ) + 2 - 1 / ((n : ℝ) + 1)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max s s⁻¹)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : max s s⁻¹ < n := hN.trans_le (by exact_mod_cast hn)
  have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  constructor
  · rw [zero_add, one_div, inv_le_comm₀ (by positivity) hs]
    linarith [le_max_right s s⁻¹]
  · linarith [le_max_left s s⁻¹]

/-- Test fields `X_n` with `|X_n| ≤ 1` and `t X_n(t) → |t|`: `X_n(t) = ψ_n(t) − ψ_n(−t)` for
smooth plateaus `ψ_n` vanishing outside `(0, n + 2)` and equal to `1` on
`[1/(n+1), n + 2 − 1/(n+1)]` (`TauCeti.exists_contDiff_plateau`). -/
private theorem exists_tendsto_mul_testFunction :
    ∃ X : ℕ → 𝓓((⊤ : Opens ℝ), ℝ), (∀ n x, ‖X n x‖ ≤ 1) ∧
      ∀ t, Tendsto (fun n => t * X n t) atTop (𝓝 |t|) := by
  choose ψ hψc hψ0 hψ1 hψout hψin _ using fun n : ℕ =>
    exists_contDiff_plateau (a := 0) (b := (n : ℝ) + 2) (δ := 1 / ((n : ℝ) + 1)) (by positivity)
  have hneg (n : ℕ) {t : ℝ} (ht : t ≤ 0) : ψ n t = 0 := hψout n t fun h => ht.not_gt h.1
  refine ⟨fun n => ⟨fun t => ψ n t - ψ n (-t), (hψc n).sub ((hψc n).comp contDiff_neg),
    HasCompactSupport.intro (K := Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2)) isCompact_Icc fun t ht => ?_,
    by simp⟩, fun n t => ?_, fun t => ?_⟩
  · rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · rw [hneg n (by linarith), hψout n (-t) fun h => by linarith [h.2], sub_self]
    · rw [hψout n t (fun h => by linarith [h.2]), hneg n (by linarith), sub_self]
  · rw [coe_mk, Real.norm_eq_abs]
    rcases le_total t 0 with ht | ht
    · rw [hneg n ht, zero_sub, abs_neg, abs_of_nonneg (hψ0 n _)]
      exact hψ1 n _
    · rw [hneg n (neg_nonpos.2 ht), sub_zero, abs_of_nonneg (hψ0 n _)]
      exact hψ1 n _
  · simp_rw [coe_mk]
    refine tendsto_const_nhds.congr' ?_
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · filter_upwards [eventually_mem_Icc_one_div (neg_pos.2 ht)] with n hn
      rw [hneg n ht.le, hψin n _ hn, abs_of_neg ht]
      ring
    · simp
    · filter_upwards [eventually_mem_Icc_one_div ht] with n hn
      rw [hψin n _ hn, hneg n (by linarith), abs_of_pos ht]
      ring

/-- **Perimeter of the line against `γ`.** With the measure `γ` in place of `volume`, the whole
line has perimeter `√(2/π) ≈ 0.7979`; contrast `TauCeti.gaussianPerimeter_univ`, by which its
Gaussian perimeter is `0`. -/
theorem perimeter_gaussianReal_univ :
    perimeter (gaussianReal 0 1) ⊤ (univ : Set ℝ) = ENNReal.ofReal √(2 / Real.pi) := by
  have habs : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  have hmean : ∫ x, |x| ∂gaussianReal 0 1 = √(2 / Real.pi) := by
    simpa using TauCeti.Probability.integral_abs_gaussianReal 1
  have hint (X : 𝓓((⊤ : Opens ℝ), ℝ)) (hX : ∀ x, ‖X x‖ ≤ 1) :
      Integrable (fun x => x * X x) (gaussianReal 0 1) :=
    habs.mono' (continuous_id.mul X.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg x) (hX x))
  rw [perimeter_gaussianReal_univ_eq_iSup, ← hmean]
  refine le_antisymm (iSup₂_le fun X hX => ENNReal.ofReal_le_ofReal ?_) ?_
  · refine integral_mono (hint X hX) habs fun x => ?_
    calc x * X x ≤ |x * X x| := le_abs_self _
      _ ≤ |x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg x) (by simpa using hX x)
  · obtain ⟨X, hX1, hXlim⟩ := exists_tendsto_mul_testFunction
    have hlim : Tendsto (fun n : ℕ => ∫ x, x * X n x ∂gaussianReal 0 1) atTop
        (𝓝 (∫ x, |x| ∂gaussianReal 0 1)) :=
      tendsto_integral_of_dominated_convergence (fun x => |x|)
        (fun n => (continuous_id.mul (X n).continuous).aestronglyMeasurable) habs
        (fun n => Eventually.of_forall fun x => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_of_le_one_right (abs_nonneg x) (by simpa using hX1 n x))
        (Eventually.of_forall hXlim)
    exact le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun n => le_iSup₂_of_le
      (f := fun (X : 𝓓((⊤ : Opens ℝ), ℝ)) (_ : ∀ x, ‖X x‖ ≤ 1) =>
        ENNReal.ofReal (∫ x, x * X x ∂gaussianReal 0 1)) (X n) (hX1 n) le_rfl

/-- Against `γ`, the empty set has perimeter `0` while its complement `ℝ` has positive perimeter:
this perimeter is not complement invariant. -/
example : perimeter (gaussianReal 0 1) ⊤ (∅ : Set ℝ) = 0 :=
  perimeter_empty

/-- The Gaussian perimeter of the whole line is `0`. -/
example : gaussianPerimeter (univ : Set ℝ) = 0 :=
  gaussianPerimeter_univ

end TauCeti.Examples.GaussianMeasurePerimeter

end
