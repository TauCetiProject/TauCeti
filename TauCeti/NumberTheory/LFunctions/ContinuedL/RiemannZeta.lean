/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.ContinuedL.Basic
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
import TauCeti.Analysis.Meromorphic.NormalForm

/-!
# The continued L-function of the Riemann zeta record

Specializing `AnalyticLFunctionData.continuedL` to `riemannZetaData` recovers Mathlib's
`riemannZeta` pointwise on all of `ℂ`:

* Off `0` and `1`, `riemannZetaData.polarOrder s = 0` and `completedRiemannZeta s * (Gammaℝ s)⁻¹ =
  riemannZeta s` (`riemannZeta_def_of_ne_zero`), including at the trivial zeros `-2, -4, …`.
* At `s = 1`, `Gammaℝ 1 ≠ 0`, so `meromorphicOrderAt invGammaFactor 1 = 0 < 1 = polarOrder 1` and
  `continuedL` retains `completedRiemannZeta 1 / Gammaℝ 1 = riemannZeta 1`.
* At `s = 0`, the simple pole of `completedRiemannZeta` is cancelled by the simple zero of
  `(Gammaℝ)⁻¹`, and the normal-form extension evaluates to the punctured limit `riemannZeta 0 =
  -1 / 2` rather than the raw quotient `0`.
-/

public section

open Complex Filter Topology

namespace TauCeti.LFunctions

private theorem riemannZetaData_raw_eq_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    ((riemannZetaData.conductor : ℕ) : ℂ) ^ (-z / 2) * riemannZetaData.completed z *
        riemannZetaData.invGammaFactor z = riemannZeta z := by
  rw [riemannZetaData_conductor, PNat.val_ofNat, Nat.cast_one, one_cpow, one_mul,
    riemannZetaData_completed, AnalyticLFunctionData.invGammaFactor_def,
    riemannZetaData_gammaFactor, riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]

private theorem riemannZetaData_continuedL_eq_at_zero :
    riemannZetaData.continuedL 0 = riemannZeta 0 := by
  set R : ℂ → ℂ := fun z ↦ ((riemannZetaData.conductor : ℕ) : ℂ) ^ (-z / 2) *
    riemannZetaData.completed z * riemannZetaData.invGammaFactor z
  have hlim : Tendsto R (𝓝[≠] 0) (𝓝 (riemannZeta 0)) := by
    have hcont : ContinuousAt riemannZeta 0 :=
      (differentiableAt_riemannZeta (by norm_num : (0 : ℂ) ≠ 1)).continuousAt
    exact hcont.continuousWithinAt.tendsto.congr'
      (eventually_nhdsWithin_of_forall fun z hz ↦ (riemannZetaData_raw_eq_of_ne_zero hz).symm)
  have hmR : MeromorphicAt R 0 :=
    (riemannZetaData_hasMeromorphicContinuation.meromorphic_continuedL 0).congr
      (riemannZetaData.continuedL_eventuallyEq 0)
  have hordR : 0 ≤ meromorphicOrderAt R 0 :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hmR).1 ⟨riemannZeta 0, hlim⟩
  have hp0 : riemannZetaData.polarOrder 0 = 1 := by simp
  have hle : (riemannZetaData.polarOrder 0 : WithTop ℤ) ≤
      meromorphicOrderAt riemannZetaData.invGammaFactor 0 := by
    rw [← meromorphicOrderAt_congr (riemannZetaData.continuedL_eventuallyEq 0),
      AnalyticLFunctionData.meromorphicOrderAt_continuedL
        (riemannZetaData_hasMeromorphicContinuation.meromorphic 0),
      riemannZetaData_hasMeromorphicContinuation.meromorphicOrderAt_eq 0 (by simp),
      hp0, Nat.cast_one, sub_eq_add_neg,
      ← riemannZetaData.meromorphicOrderAt_invGammaFactor] at hordR
    cases hγ : meromorphicOrderAt riemannZetaData.invGammaFactor 0 with
    | top => exact le_top
    | coe m =>
      rw [hγ] at hordR
      rw [hp0, Nat.cast_one]
      norm_cast at hordR ⊢
      omega
  rw [riemannZetaData.continuedL_eq_toMeromorphicNFAt (by simp) hle]
  exact hmR.toMeromorphicNFAt_apply_eq_of_tendsto hlim

/-- **The continued L-function of `riemannZetaData` is `riemannZeta`**, pointwise at every `s : ℂ`
(including both `s = 0` and `s = 1`). -/
@[simp]
theorem riemannZetaData_continuedL : riemannZetaData.continuedL = riemannZeta := by
  ext s
  by_cases hs0 : s = 0
  · subst s
    exact riemannZetaData_continuedL_eq_at_zero
  · by_cases hs1 : s = 1
    · subst s
      rw [riemannZetaData.continuedL_eq_of_gammaFactor_ne_zero
          (by rw [riemannZetaData_gammaFactor]; exact Gammaℝ_ne_zero_of_re_pos (by simp)),
        ← AnalyticLFunctionData.invGammaFactor_def]
      exact riemannZetaData_raw_eq_of_ne_zero one_ne_zero
    · have hp : riemannZetaData.polarOrder s = 0 := by simp [hs0, hs1]
      rw [riemannZetaData.continuedL_eq_of_polarOrder_eq_zero hp]
      exact riemannZetaData_raw_eq_of_ne_zero hs0

/-- Pointwise form of `riemannZetaData_continuedL`. -/
theorem riemannZetaData_continuedL_apply (s : ℂ) :
    riemannZetaData.continuedL s = riemannZeta s :=
  congrFun riemannZetaData_continuedL s

/-- At `s = 0`, `riemannZetaData.continuedL` recovers `ζ(0) = -1 / 2`, whereas the raw product
`completedRiemannZeta 0 * (Gammaℝ 0)⁻¹` is `0`. -/
theorem riemannZetaData_continuedL_zero : riemannZetaData.continuedL 0 = -1 / 2 := by
  rw [riemannZetaData_continuedL_apply, riemannZeta_zero]

/-- At negative even integers `-2 * (n + 1)`, `riemannZetaData.continuedL` vanishes (the trivial
zeros of `ζ`), whereas `completedRiemannZeta` has order `0` there. -/
theorem riemannZetaData_continuedL_neg_two_mul_nat_add_one (n : ℕ) :
    riemannZetaData.continuedL (-2 * ((n : ℂ) + 1)) = 0 := by
  rw [riemannZetaData_continuedL_apply, riemannZeta_neg_two_mul_nat_add_one]

end TauCeti.LFunctions
