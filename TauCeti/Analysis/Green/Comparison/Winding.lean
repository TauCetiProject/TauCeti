/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Weighted
public import TauCeti.Analysis.Green.Winding
public import TauCeti.Analysis.Green.WindingWeight.Domain

/-!
# Winding-weighted Green as canonical manifold integration

The winding-weighted exterior derivative is an actual compactly supported integrable rough
top form. Its canonical oriented manifold integral equals AC circulation. The winding weight
vanishes outside the field domain, where no differentiability of the field is needed.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

/-- AC winding-weighted Green agrees with the actual canonical integral of the manifold
exterior derivative. Both boundary and intrinsic top-form integrability are conclusions. -/
theorem green_ac_winding_integralTopForm {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ}
    {P Q : ℂ → ℝ} (hab : a < b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) (hU : IsOpen U) (htrace : γ '' uIcc a b ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0) :
    IntervalIntegrable (circulationFun P Q γ) volume a b ∧
      IntegrableTopForm (I := 𝓘(ℝ, ℂ))
        (fun z ↦ windingWeight γ a b z • mextDeriv (manifoldOneForm P Q) z) ∧
      (∫ t in a..b, circulationFun P Q γ t) =
        integralTopForm (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
          (by simp))
          (fun z ↦ windingWeight γ a b z • mextDeriv (manifoldOneForm P Q) z) := by
  have hgreen := green_ac_winding hab hγ hclosed hU htrace hP hQ hindex
  have hform := HasCompactSupport.weighted_mextDeriv_integralTopForm
    (hγ.hasCompactSupport_windingWeight hclosed) hU.measurableSet
    (fun z hz ↦ ((hP z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
    (fun z hz ↦ ((hQ z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
    hgreen.2.1
  rw [indicator_windingWeight_eq_self hindex] at hform
  exact ⟨hgreen.1, hform.1, hgreen.2.2.trans hform.2.symm⟩

end TauCeti.Green
