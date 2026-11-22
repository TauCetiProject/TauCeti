/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold

/-!
# Translations of the domain and the Floer energy with a manifold target

Translating a map `u : ℝ × ℝ → M` and its perturbation data by `v` translates the Floer energy
density (`TauCeti.SmoothTwoForm.floerEnergyDensity_comp_add_right`). This file draws the two
consequences used for Floer cylinders: translations preserve the energy, and for a Hamiltonian
`H_t` of period one in `t` the energy density of `H_t dt` along a map of period one in `t` has
period one in `t`.

## Main results

* `TauCeti.SmoothTwoForm.lintegral_floerEnergyDensity_comp_add_right`: the energy of the translate
  over `(· + v) ⁻¹' S` is the energy of the original map over `S`.
* `TauCeti.SmoothTwoForm.floerEnergyDensity_add_one`: the energy density of a cylinder of period
  one in `t`, for a Hamiltonian of period one in time, has period one in `t`.
-/

public section

open Function MeasureTheory
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Translations preserve the energy.** Translating the map and the perturbation data by `v`
preserves the energy: the energy of the translate over `(· + v) ⁻¹' S` is the energy of the
original over `S`. -/
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
