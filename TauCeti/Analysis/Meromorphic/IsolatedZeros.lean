/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Codiscrete logarithmic product splitting for meromorphic functions

By `MeromorphicOn.codiscreteWithin_setOfPred_ne_zero`, two meromorphic functions `f, g : 𝕜 → 𝕜` of
finite meromorphic order on `U` are nonzero (and finite) off a discrete subset of `U`. Outside that
discrete subset, `Real.log ‖f z * g z‖ = Real.log ‖f z‖ + Real.log ‖g z‖`, so
`Real.log ‖f z‖ + Real.posLog ‖g z‖` agrees along `codiscreteWithin U` with
`max (Real.log ‖f z‖) (Real.log ‖f z * g z‖)`.
-/

public section

open Filter

/-- For meromorphic functions `f, g : 𝕜 → 𝕜` of finite meromorphic order on `U`, off a discrete
subset of `U` (where neither vanishes nor has a pole), `log ‖f z‖ + log⁺ ‖g z‖` agrees with
`max (log ‖f z‖) (log ‖f z * g z‖)`. -/
theorem MeromorphicOn.eventuallyEq_codiscreteWithin_log_norm_add_posLog
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {f g : 𝕜 → 𝕜}
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hord_f : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤)
    (hord_g : ∀ u ∈ U, meromorphicOrderAt g u ≠ ⊤) :
    ((fun z ↦ Real.log ‖f z‖) + fun z ↦ Real.posLog ‖g z‖) =ᶠ[codiscreteWithin U]
      fun z ↦ max (Real.log ‖f z‖) (Real.log ‖f z * g z‖) := by
  filter_upwards [hf.codiscreteWithin_setOfPred_ne_zero hord_f,
    hg.codiscreteWithin_setOfPred_ne_zero hord_g] with z hzf hzg
  simp [Pi.add_apply, Real.posLog_apply, add_max, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hzf) (norm_ne_zero_iff.mpr hzg)]

example {𝕜 : Type*} [NontriviallyNormedField 𝕜] (U : Set 𝕜) :
    ((fun z : 𝕜 ↦ Real.log ‖(fun _ ↦ (1 : 𝕜)) z‖) +
      fun z ↦ Real.posLog ‖(fun _ ↦ (1 : 𝕜)) z‖) =ᶠ[codiscreteWithin U]
      fun z ↦ max (Real.log ‖(fun _ ↦ (1 : 𝕜)) z‖)
        (Real.log ‖(fun _ ↦ (1 : 𝕜)) z * (fun _ ↦ (1 : 𝕜)) z‖) := by
  have hord : ∀ u ∈ U, meromorphicOrderAt (fun _ : 𝕜 ↦ (1 : 𝕜)) u ≠ ⊤ := fun u _ ↦ by
    rw [analyticAt_const.meromorphicOrderAt_eq,
      analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero]
    simp
  exact analyticOnNhd_const.meromorphicOn.eventuallyEq_codiscreteWithin_log_norm_add_posLog
    analyticOnNhd_const.meromorphicOn hord hord
