/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Mellin transforms of decaying exponentials, and their congruence on `(0, ∞)`

For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`
(`TauCeti.mellinConvergent_exp_neg_mul`). At `c = 1` this is the convergence of Euler's integral
for `Γ(z)` (`Complex.GammaIntegral_convergent`), and the scaling `t ↦ c t` is Mathlib's
`MellinConvergent.comp_mul_left`. Its value `c^(-z) Γ(z)` is Mathlib's
`Complex.integral_cpow_mul_exp_neg_mul_Ioi`. These are the gamma integrals produced by Gaussians
`e^(-π a² t)` in Hecke's integral representations of zeta and L-functions.

The Mellin transform reads a function only on `(0, ∞)`, so functions agreeing there have the same
transform, with the same convergence (`TauCeti.hasMellin_congr`). Kernels that are extended by zero
off `(0, ∞)` are compared with their unextended forms this way.
-/

public section

open Complex Set

namespace TauCeti

/-- Functions that agree on `(0, ∞)` have the same Mellin transform, with the same convergence. -/
theorem hasMellin_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℝ → E}
    (h : EqOn f g (Ioi 0)) {s : ℂ} {m : E} : HasMellin f s m ↔ HasMellin g s m := by
  have h' : EqOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f t) (fun t ↦ (t : ℂ) ^ (s - 1) • g t)
      (Ioi 0) := fun t ht ↦ by simp only [h ht]
  simp only [HasMellin, MellinConvergent, mellin,
    MeasureTheory.integrableOn_congr_fun h' measurableSet_Ioi,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h']

/-- For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`. -/
theorem mellinConvergent_exp_neg_mul {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) z := by
  refine (MellinConvergent.comp_mul_left (f := fun t : ℝ ↦ (Real.exp (-t) : ℂ)) hc).mpr ?_
  exact (GammaIntegral_convergent hz).congr_fun (fun t _ ↦ mul_comm _ _) measurableSet_Ioi

end TauCeti
