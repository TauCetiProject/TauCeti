/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Translations preserve the curvature allowance and the energy, for a manifold target

Translating the domain `ℝ × ℝ` by `v` translates the curvature, the perturbed derivative and the
energy density of a map into a manifold with a two-form
(`TauCeti.SmoothTwoForm.hamiltonianCurvature_comp_add_right`,
`TauCeti.SmoothTwoForm.floerEnergyDensity_comp_add_right`). Since translations preserve Lebesgue
measure, they preserve the integrated quantities.

## Main results

* `SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_comp_add_right`: translations of the domain
  preserve the curvature allowance along a map.
* `SmoothTwoForm.lintegral_floerEnergyDensity_comp_add_right`: translations of the domain preserve
  the energy along a map, over corresponding sets.

For a constant form, `SymplecticForm.floerEnergyDensity_constSmooth` turns these into the
statements for a symplectic vector space.
-/

public section

open MeasureTheory
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- Translations of the domain preserve the integrated curvature along a map. -/
theorem lintegral_enorm_hamiltonianCurvature_comp_add_right (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (v : ℝ × ℝ) :
    ∫⁻ z, ‖ω.hamiltonianCurvature (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) z (u (z + v))‖ₑ =
      ∫⁻ z, ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ := by
  have hv : MeasurePreserving (· + v) volume volume :=
    (measurePreserving_add_right volume v.1).prod (measurePreserving_add_right volume v.2)
  simp only [hamiltonianCurvature_comp_add_right]
  exact hv.lintegral_comp_emb (measurableEmbedding_addRight v)
    (fun z ↦ ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ)

/-- **Translations preserve the energy.** The energy of the translate of the map and the
perturbation data by `v` over `(· + v) ⁻¹' S` is the energy of the original over `S`. -/
theorem lintegral_floerEnergyDensity_comp_add_right (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (v : ℝ × ℝ) (S : Set (ℝ × ℝ)) :
    ∫⁻ z in (· + v) ⁻¹' S, ENNReal.ofReal
        (ω.floerEnergyDensity (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z) =
      ∫⁻ z in S, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z) := by
  have hv : MeasurePreserving (· + v) volume volume :=
    (measurePreserving_add_right volume v.1).prod (measurePreserving_add_right volume v.2)
  simp only [floerEnergyDensity_comp_add_right]
  exact hv.setLIntegral_comp_preimage_emb (measurableEmbedding_addRight v)
    (fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity Ks Kt u z)) S

end TauCeti.SmoothTwoForm
