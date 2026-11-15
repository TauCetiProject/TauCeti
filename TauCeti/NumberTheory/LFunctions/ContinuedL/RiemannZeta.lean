/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.ContinuedL.Basic
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta

/-!
# The continued L-function of the Riemann zeta record

Specializing `AnalyticLFunctionData.continuedL` to `riemannZetaData` recovers Mathlib's
`riemannZeta` pointwise on all of `ℂ`:

* Off `0` and `1`, `riemannZetaData.polarOrder s = 0` and `completedRiemannZeta s * (Gammaℝ s)⁻¹ =
  riemannZeta s` (`riemannZeta_def_of_ne_zero`), including at the trivial zeros `-2, -4, …`.
* At `s = 1`, `Gammaℝ 1 ≠ 0`, so `meromorphicOrderAt invGammaFactor 1 = 0 < 1 = polarOrder 1` and
  `continuedL` retains `completedRiemannZeta 1 / Gammaℝ 1 = riemannZeta 1`.
* At `s = 0`, the simple pole of `completedRiemannZeta` is cancelled by the simple zero of
  `(Gammaℝ)⁻¹`, and `HasMeromorphicContinuation.continuedL_eq_of_tendsto` evaluates `continuedL`
  to the punctured limit `riemannZeta 0 = -1 / 2` rather than the raw quotient `0`.
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

private theorem riemannZetaData_continuedL_eq_of_ne_zero {s : ℂ} (hs0 : s ≠ 0) :
    riemannZetaData.continuedL s = riemannZeta s := by
  by_cases hs1 : s = 1
  · subst s
    rw [riemannZetaData.continuedL_eq_of_gammaFactor_ne_zero
        (by rw [riemannZetaData_gammaFactor]; exact Gammaℝ_ne_zero_of_re_pos (by simp)),
      ← AnalyticLFunctionData.invGammaFactor_def]
    exact riemannZetaData_raw_eq_of_ne_zero one_ne_zero
  · rw [riemannZetaData.continuedL_eq_of_polarOrder_eq_zero (by simp [hs0, hs1])]
    exact riemannZetaData_raw_eq_of_ne_zero hs0

/-- **The continued L-function of `riemannZetaData` is `riemannZeta`**, pointwise at every `s : ℂ`
(including both `s = 0` and `s = 1`). -/
@[simp]
theorem riemannZetaData_continuedL : riemannZetaData.continuedL = riemannZeta := by
  ext s
  rcases eq_or_ne s 0 with rfl | hs0
  · have hcont : ContinuousAt riemannZeta 0 :=
      (differentiableAt_riemannZeta zero_ne_one).continuousAt
    exact riemannZetaData_hasMeromorphicContinuation.continuedL_eq_of_tendsto <|
      hcont.continuousWithinAt.tendsto.congr'
        (eventually_nhdsWithin_of_forall fun _ hz ↦
          (riemannZetaData_continuedL_eq_of_ne_zero hz).symm)
  · exact riemannZetaData_continuedL_eq_of_ne_zero hs0

/-! ### Checks -/

/-- At `s = 0`, `riemannZetaData.continuedL` recovers `ζ(0) = -1 / 2`, whereas the raw product
`completedRiemannZeta 0 * (Gammaℝ 0)⁻¹` is `0`. -/
example : riemannZetaData.continuedL 0 = -1 / 2 ∧
    completedRiemannZeta 0 * (Gammaℝ 0)⁻¹ = 0 := by
  simp [riemannZeta_zero, Gammaℝ_def]

/-- At negative even integers `-2 * (n + 1)`, `riemannZetaData.continuedL` vanishes (the trivial
zeros of `ζ`), whereas `completedRiemannZeta` has meromorphic order `0` there. -/
example (n : ℕ) : riemannZetaData.continuedL (-2 * ((n : ℂ) + 1)) = 0 ∧
    meromorphicOrderAt completedRiemannZeta (-2 * ((n : ℂ) + 1)) = 0 :=
  ⟨by rw [riemannZetaData_continuedL, riemannZeta_neg_two_mul_nat_add_one],
    TauCeti.meromorphicOrderAt_completedRiemannZeta_neg_two_mul_nat_add_one n⟩

end TauCeti.LFunctions
