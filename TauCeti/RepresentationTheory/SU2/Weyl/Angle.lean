/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.Weyl.Integration

/-!
# Haar probability in the conjugacy angle

In the coordinate given by `TauCeti.SU2.conjugacyAngle`, Haar probability on `SU(2)` has density
`(2/π) sin² θ` on `[0, π]`.

See K. S. Kedlaya, *Notes on analytic number theory*, §24.5.
-/

public section

open MeasureTheory

namespace TauCeti.SU2

/-- Integrating a real continuous test function of the angle against Haar probability gives the
integral against the density `(2/π) sin² θ` on the closed Weyl chamber. -/
theorem integral_comp_conjugacyAngle {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 Real.pi)) :
    ∫ g, f (conjugacyAngle g) ∂haarProb SU2 =
      (2 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, f θ * Real.sin θ ^ 2 := by
  have hcont : Continuous (f ∘ conjugacyAngle) :=
    hf.comp_continuous continuous_conjugacyAngle conjugacyAngle_mem_Icc
  have h := weyl_integration_formula (Complex.continuous_ofReal.comp hcont) (fun u g ↦ by
    have hc : IsConj g (u * g * u⁻¹) := isConj_iff.mpr ⟨u, rfl⟩
    simpa only [Function.comp_apply] using
      congrArg (fun θ ↦ (f θ : ℂ)) (conjugacyAngle_eq_of_isConj hc).symm)
  have hfactor :
      ∫ θ in (0 : ℝ)..Real.pi,
        (f (conjugacyAngle (torusExp θ)) : ℂ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) =
      4 * ((∫ θ in (0 : ℝ)..Real.pi, f θ * Real.sin θ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ hθ ↦ ?_
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    rw [conjugacyAngle_torusExp hθ]
    push_cast
    ring
  simp only [Function.comp_apply, Function.comp_def, integral_complex_ofReal, hfactor] at h
  calc
    ∫ g, f (conjugacyAngle g) ∂haarProb SU2 =
        (1 / (2 * Real.pi)) * (4 * ∫ θ in (0 : ℝ)..Real.pi, f θ * Real.sin θ ^ 2) := by
      exact_mod_cast h
    _ = _ := by ring

end TauCeti.SU2
