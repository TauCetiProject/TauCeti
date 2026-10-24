/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.LieDeriv
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Normed.Module.Alternating.Basic

/-!
# Time derivatives of differential forms pulled back along a flow

Let `X : 𝕜 → E → E` be a time-dependent vector field on a normed space and `ψ : 𝕜 → E → E` a
family of maps moving along it: `∂ₜ ψₜ x = Xₜ (ψₜ x)`, and the derivative `Dψₜ x` solves the
variational equation `∂ₜ Dψₜ x = DXₜ (ψₜ x) ∘ Dψₜ x`. The time-dependent flow of a `C¹` field has
both properties. For a time-dependent differential form `ω : 𝕜 → E → E [⋀^Fin k]→L[𝕜] F`, the
pullback `ψₜ^* ωₜ` at `x` is `(ωₜ (ψₜ x)).compContinuousLinearMap (Dψₜ x)`, and

`∂ₜ (ψₜ^* ωₜ) = ψₜ^* (∂ₜ ωₜ + L_{Xₜ} ωₜ)`,

where `L` is the Lie derivative `TauCeti.lieDerivForm`. Consequently `ψₜ^* ωₜ` does not depend
on `t` when `∂ₜ ωₜ + L_{Xₜ} ωₜ` vanishes along the orbit of `x`. This is the identity behind
Moser's deformation argument; for an autonomous field and a time-independent form it is the flow
characterization of the Lie derivative.

The statements are pointwise in `x`: only the orbit of `x` and the derivative of `ψₜ` at `x`
enter, so no global flow or global regularity is required.

## Main declarations

* `TauCeti.hasDerivAt_compContinuousLinearMap_fderiv`: the derivative formula above.
* `TauCeti.compContinuousLinearMap_fderiv_eq_of_deriv_add_lieDerivForm_eq_zero`: the pullbacks
  at the two ends of an interval agree when `∂ₜ ωₜ + L_{Xₜ} ωₜ` vanishes along the orbit.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 12.37 (Lie derivatives along
  flows) and Chapter 22 (the time-dependent formula in the proof of Darboux's theorem).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

open Set ContinuousAlternatingMap

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {k : ℕ}

/-- **The time derivative of a pulled-back form.** If `ψₜ` moves along the time-dependent field
`Xₜ` and its derivative at `x` solves the variational equation, then the pullback
`ψₜ^* ωₜ = (ωₜ (ψₜ x)).compContinuousLinearMap (Dψₜ x)` has time derivative
`ψₜ^* (∂ₜ ωₜ + L_{Xₜ} ωₜ)`. -/
theorem hasDerivAt_compContinuousLinearMap_fderiv {ω : 𝕜 → E → E [⋀^Fin k]→L[𝕜] F}
    {ψ X : 𝕜 → E → E} {x : E} {t : 𝕜}
    (hω : DifferentiableAt 𝕜 (fun p : 𝕜 × E ↦ ω p.1 p.2) (t, ψ t x))
    (hψ : HasDerivAt (fun s ↦ ψ s x) (X t (ψ t x)) t)
    (hDψ : HasDerivAt (fun s ↦ fderiv 𝕜 (ψ s) x)
      (fderiv 𝕜 (X t) (ψ t x) ∘L fderiv 𝕜 (ψ t) x) t) :
    HasDerivAt (fun s ↦ (ω s (ψ s x)).compContinuousLinearMap (fderiv 𝕜 (ψ s) x))
      ((deriv (fun s ↦ ω s (ψ t x)) t + lieDerivForm (X t) (ω t) (ψ t x)).compContinuousLinearMap
        (fderiv 𝕜 (ψ t) x)) t := by
  -- The derivative of `s ↦ ωₛ (ψₛ x)` splits into the time and the space derivative of `ω`.
  have hf := hasDerivAt_comp_prodMk hω hψ
  rw [← (hasDerivAt_parameterCurve hω).deriv, ← fderiv_timeSlice hω] at hf
  replace hf := hf.hasFDerivAt
  have h := hf.continuousAlternatingMapCompContinuousLinearMap hDψ.hasFDerivAt
  rw [hasDerivAt_iff_hasFDerivAt]
  convert h using 1
  ext1
  ext v
  simp [lieDerivForm_def, fderivCompContinuousLinearMap_comp, add_assoc]

/-- **Invariance of pulled-back forms.** If `ψₜ` moves along `Xₜ`, its derivative at `x` solves
the variational equation, and `∂ₜ ωₜ + L_{Xₜ} ωₜ` vanishes along the orbit of `x` for
`t ∈ [a, b]`, then the pullbacks `ψₐ^* ωₐ` and `ψ_b^* ω_b` at `x` agree. -/
theorem compContinuousLinearMap_fderiv_eq_of_deriv_add_lieDerivForm_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ω : ℝ → E → E [⋀^Fin k]→L[ℝ] F} {ψ X : ℝ → E → E} {x : E} {a b : ℝ}
    (hab : a ≤ b)
    (hω : ∀ t ∈ Icc a b, DifferentiableAt ℝ (fun p : ℝ × E ↦ ω p.1 p.2) (t, ψ t x))
    (hψ : ∀ t ∈ Icc a b, HasDerivAt (fun s ↦ ψ s x) (X t (ψ t x)) t)
    (hDψ : ∀ t ∈ Icc a b, HasDerivAt (fun s ↦ fderiv ℝ (ψ s) x)
      (fderiv ℝ (X t) (ψ t x) ∘L fderiv ℝ (ψ t) x) t)
    (hzero : ∀ t ∈ Icc a b,
      deriv (fun s ↦ ω s (ψ t x)) t + lieDerivForm (X t) (ω t) (ψ t x) = 0) :
    (ω b (ψ b x)).compContinuousLinearMap (fderiv ℝ (ψ b) x) =
      (ω a (ψ a x)).compContinuousLinearMap (fderiv ℝ (ψ a) x) := by
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivAt (fun s ↦ (ω s (ψ s x)).compContinuousLinearMap (fderiv ℝ (ψ s) x)) 0 t := by
    intro t ht
    have h := hasDerivAt_compContinuousLinearMap_fderiv (hω t ht) (hψ t ht) (hDψ t ht)
    rwa [hzero t ht, ← compContinuousLinearMapCLM_apply, _root_.map_zero] at h
  refine constant_of_has_deriv_right_zero (fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt) b ⟨hab, le_rfl⟩

end TauCeti
