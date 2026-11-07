/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The Mellin transform of a decaying exponential

For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`
(`TauCeti.mellinConvergent_exp_neg_mul`). At `c = 1` this is the convergence of Euler's integral
for `Γ(z)` (`Complex.GammaIntegral_convergent`), and the scaling `t ↦ c t` is Mathlib's
`MellinConvergent.comp_mul_left`. Its value `c^(-z) Γ(z)` is Mathlib's
`Complex.integral_cpow_mul_exp_neg_mul_Ioi`. These are the gamma integrals produced by Gaussians
`e^(-π a² t)` in Hecke's integral representations of zeta and L-functions.
-/

public section

open Complex Set

namespace TauCeti

/-- For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`. -/
theorem mellinConvergent_exp_neg_mul {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) z := by
  refine (MellinConvergent.comp_mul_left (f := fun t : ℝ ↦ (Real.exp (-t) : ℂ)) hc).mpr ?_
  exact (GammaIntegral_convergent hz).congr_fun (fun t _ ↦ mul_comm _ _) measurableSet_Ioi

end TauCeti
