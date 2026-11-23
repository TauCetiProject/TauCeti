/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Mellin transforms of exponential and continuous cutoff kernels

For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`
(`TauCeti.mellinConvergent_exp_neg_mul`). At `c = 1` this is the convergence of Euler's integral
for `Γ(z)` (`Complex.GammaIntegral_convergent`), and the scaling `t ↦ c t` is Mathlib's
`MellinConvergent.comp_mul_left`. Its value `c^(-z) Γ(z)` is Mathlib's
`Complex.integral_cpow_mul_exp_neg_mul_Ioi`. These are the gamma integrals produced by Gaussians
`e^(-π a² t)` in Hecke's integral representations of zeta and L-functions.

`TauCeti.hasMellin_max_one_sub_zero` computes the Mellin transform of the continuous cutoff
`max (1 - t) 0`, using the difference of Mathlib's interval-power transforms. Its inverse
transform gives the first-order Perron weight.
-/

public section

open Complex Set

namespace TauCeti

/-- The Mellin transform of the continuous cutoff `max (1 - t) 0` is `1 / (s(s+1))`
for `0 < Re s`. Only its values on `(0, ∞)` contribute to the transform. -/
theorem hasMellin_max_one_sub_zero {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t : ℝ ↦ ((max (1 - t) 0 : ℝ) : ℂ)) s ((s * (s + 1))⁻¹) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (by simpa using (by linarith : 0 < s.re + 1))
  have hh := hasMellin_sub h0.1 h1.1
  rw [h0.2, h1.2] at hh
  refine (hasMellin_congr (f := fun t ↦
    (Ioc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℂ)) t -
      (Ioc (0 : ℝ) 1).indicator (fun u ↦ (u : ℂ) ^ (1 : ℂ)) t) ?_).mp ?_
  · intro t ht
    have ht0 : 0 < t := Set.mem_Ioi.mp ht
    by_cases h : t ≤ 1
    · simp [ht0, h]
    · have ht1 : 1 - t ≤ 0 := by linarith
      simp [h, max_eq_right ht1]
  · have hs0 : s ≠ 0 := by intro h; simp [h] at hs
    have hs1 : s + 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    refine ⟨hh.1, hh.2.trans ?_⟩
    field_simp [hs0, hs1]
    ring

/-- For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`. -/
theorem mellinConvergent_exp_neg_mul {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) z := by
  refine (MellinConvergent.comp_mul_left (f := fun t : ℝ ↦ (Real.exp (-t) : ℂ)) hc).mpr ?_
  exact (GammaIntegral_convergent hz).congr_fun (fun t _ ↦ mul_comm _ _) measurableSet_Ioi

end TauCeti
