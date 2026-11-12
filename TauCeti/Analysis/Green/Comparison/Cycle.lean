/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Weighted
public import TauCeti.Analysis.Green.Cycle

/-!
# Existing contour cycles as canonical manifold integrals

The existing cycle winding number, set to zero on the cycle trace, multiplies the actual manifold
exterior derivative. Its canonical oriented integral is the circulation sum over the cycle's
canonical support. Generator intervals may have either orientation or coincide.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

/-- Green for an existing contour cycle agrees with the actual canonical integral of its
winding-weighted manifold exterior derivative. Both integrabilities are conclusions. -/
theorem _root_.TauCeti.Contour.Cycle.green_winding_integralTopForm (C : Contour.Cycle) {U : Set ℂ}
    {P Q : ℂ → ℝ}
    (hU : IsOpen U) (htrace : Contour.Cycle.IsIn C U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : Contour.Cycle.IsNullHomologous C U) :
    (∀ γ ∈ FreeAbelianGroup.support C,
      IntervalIntegrable (circulationFun P Q γ) volume γ.a γ.b) ∧
      IntegrableTopForm (I := 𝓘(ℝ, ℂ))
        (fun z ↦ C.windingWeight z •
            mextDeriv (manifoldOneForm P Q) z) ∧
      (∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℝ) *
        ∫ t in γ.a..γ.b, circulationFun P Q γ t) =
        integralTopForm (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
          (by simp))
          (fun z ↦ C.windingWeight z •
              mextDeriv (manifoldOneForm P Q) z) := by
  have hgreen := TauCeti.Contour.Cycle.green_winding C hU htrace hP hQ hindex
  have hform := C.hasCompactSupport_windingWeight.weighted_mextDeriv_integralTopForm
    hU.measurableSet
    (fun z hz ↦ ((hP z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
    (fun z hz ↦ ((hQ z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
    hgreen.2.1
  rw [C.indicator_windingWeight_eq_self hindex] at hform
  exact ⟨hgreen.1, hform.1, hgreen.2.2.trans hform.2.symm⟩

end TauCeti.Green
