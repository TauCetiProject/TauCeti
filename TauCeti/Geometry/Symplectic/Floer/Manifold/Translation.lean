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
* `SmoothTwoForm.floerEnergyDensity_add_one`: the energy density of a cylinder of period one in
  `t`, for a Hamiltonian of period one in time, has period one in `t`.

For a constant form, `SymplecticForm.floerEnergyDensity_constSmooth` turns these into the
statements for a symplectic vector space.
-/

public section

open Function MeasureTheory
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

/-- For a Hamiltonian `H` of period one in time, the Floer energy density of `H_t dt` along a map
`u` of period one in `t` has period one in `t`. -/
theorem floerEnergyDensity_add_one (ω : SmoothTwoForm I M) {H : ℝ → M → ℝ}
    (hHper : Periodic H 1) {u : ℝ × ℝ → M} (hper : ∀ s t, u (s, t + 1) = u (s, t)) (s t : ℝ) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s, t + 1) =
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (s, t) := by
  have hu1 : (fun w ↦ u (w + ((0 : ℝ), (1 : ℝ)))) = u :=
    funext fun ⟨s, t⟩ ↦ by simpa using hper s t
  have hH1 : (fun w : ℝ × ℝ ↦ H (w + ((0 : ℝ), (1 : ℝ))).2) = fun w ↦ H w.2 :=
    funext fun w ↦ by simpa using hHper w.2
  have h := ω.floerEnergyDensity_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) u
    ((0 : ℝ), (1 : ℝ)) (s, t)
  simp only [hu1, hH1, Prod.mk_add_mk, add_zero] at h
  exact h.symm

end TauCeti.SmoothTwoForm
