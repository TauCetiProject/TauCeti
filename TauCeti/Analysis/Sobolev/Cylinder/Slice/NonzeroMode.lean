/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder.Slice.Average
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity

/-!
# Onto the nonzero modes along a connected family

The nonzero Fourier modes of the Sobolev space `W^{1,2}(ℝ × S¹, V)` and of `L²(ℝ × S¹, V)` are the
kernels of the slice averages `TauCeti.CylinderSobolev.sliceAverageL` and
`TauCeti.StripSobolev.sliceAverageLp`. An operator `D : W^{1,2} → L²` commuting with the slice
average maps the nonzero modes into the nonzero modes. Applied to the restrictions to the nonzero
modes, the method of continuity (`IsPreconnected.surjective_iff_of_forall_norm_le`) gives the
following continuation principle.

* **Onto the nonzero modes along a connected family.** Let `D τ` be operators commuting with the
  slice average, depending continuously on `τ` in a preconnected set `s`, and bounded below on the
  nonzero modes with one constant for all `τ`. If one member maps the nonzero modes of `W^{1,2}`
  onto those of `L²`, so does every member
  (`TauCeti.CylinderSobolev.exists_eq_of_sliceAverageLp_eq_zero_of_isPreconnected`).

This applies to the linearized Floer operator along a time-independent cylinder, joined to an
invertible operator by a segment of Hamiltonians, in
`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Range`.
-/

public section

open MeasureTheory Set ContinuousLinearMap

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **Onto the nonzero modes along a connected family.** Let `D τ : W^{1,2}(ℝ × S¹, V) → L²` be
operators commuting with the slice average, depending continuously on `τ` in a preconnected set
`s`, and satisfying `‖x‖ ≤ C * ‖D τ x‖` on the nonzero modes with one constant `C` for all
`τ ∈ s`. If `D τ₀` maps the nonzero modes of `W^{1,2}` onto
those of `L²` for one `τ₀ ∈ s`, then so does every `D τ` with `τ ∈ s`. -/
theorem exists_eq_of_sliceAverageLp_eq_zero_of_isPreconnected {X : Type*} [TopologicalSpace X]
    {s : Set X} {D : X → H1 V →L[ℝ] Lp V 2 stripMeasure} (hD : ContinuousOn D s)
    (hs : IsPreconnected s) (hcomm : ∀ τ ∈ s, ∀ x, D τ (sliceAverageL x) = sliceAverageLp (D τ x))
    {C : ℝ} (hlow : ∀ τ ∈ s, ∀ x : H1 V, sliceAverageL x = 0 → ‖x‖ ≤ C * ‖D τ x‖) {τ₀ τ : X}
    (hτ₀ : τ₀ ∈ s) (h₀ : ∀ y, sliceAverageLp y = 0 → ∃ x, sliceAverageL x = 0 ∧ D τ₀ x = y)
    (hτ : τ ∈ s) {y : Lp V 2 stripMeasure} (hy : sliceAverageLp y = 0) :
    ∃ x, sliceAverageL x = 0 ∧ D τ x = y := by
  -- The nonzero modes `E` of `W^{1,2}`, inside `L²` jets, and `G` of `L²`.
  set E : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
    H1 V ⊓ (sliceAverageLp : Lp (V × V × V) 2 stripMeasure →L[ℝ] _).ker
  set G : Submodule ℝ (Lp V 2 stripMeasure) :=
    (sliceAverageLp : Lp V 2 stripMeasure →L[ℝ] Lp V 2 stripMeasure).ker
  set ι : E →L[ℝ] H1 V :=
    E.subtypeL.codRestrict (H1 V) fun x ↦ (Submodule.mem_inf.1 x.property).1
  have hι (x : E) : sliceAverageL (ι x) = 0 := by
    refine Subtype.ext ?_
    rw [coe_sliceAverageL]
    exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 x.property).2
  have hmaps (σ : s) (x : E) : (D σ).comp ι x ∈ G := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, comp_apply, ← hcomm σ σ.property, hι,
      map_zero]
  -- The restrictions `T σ` to the nonzero modes depend continuously on `σ ∈ s`.
  set T : s → E →L[ℝ] G := fun σ ↦ ((D σ).comp ι).codRestrict G (hmaps σ)
  have hcont : Continuous T := by
    have hiso : Isometry fun L : E →L[ℝ] G ↦ G.subtypeL.comp L := .of_dist_eq fun L M ↦ by
      rw [dist_eq_norm, dist_eq_norm, ← comp_sub]
      exact G.subtypeₗᵢ.norm_toContinuousLinearMap_comp
    refine hiso.comp_continuous_iff.1 ?_
    have h : (fun L : E →L[ℝ] G ↦ G.subtypeL.comp L) ∘ T = fun σ : s ↦ (D σ).comp ι :=
      funext fun σ ↦ subtypeL_comp_codRestrict _ _ _
    rw [h]
    exact (continuousOn_iff_continuous_domRestrict.1 hD).clm_comp continuous_const
  -- The restrictions satisfy the a priori estimate uniformly, and `T τ₀` is onto.
  have hH1 : IsClosed (H1 V : Set (Lp (V × V × V) 2 stripMeasure)) :=
    coe_jetClosure (testSection V) ▸ isClosed_closure
  have : CompleteSpace E := (hH1.inter (isClosed_ker _)).completeSpace_coe
  have hK : ∀ σ ∈ univ, ∀ x : E, ‖x‖ ≤ C * ‖T σ x‖ := fun σ _ x ↦ hlow σ σ.property (ι x) (hι x)
  have hsurj0 : Function.Surjective (T ⟨τ₀, hτ₀⟩) := fun z ↦ by
    obtain ⟨x, hx, hDx⟩ := h₀ z z.property
    refine ⟨⟨x, Submodule.mem_inf.2 ⟨x.property, LinearMap.mem_ker.2 ?_⟩⟩, Subtype.ext hDx⟩
    rw [ContinuousLinearMap.coe_coe, ← coe_sliceAverageL, hx, Submodule.coe_zero]
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  obtain ⟨x, hx⟩ := (isPreconnected_univ.surjective_iff_of_forall_norm_le hcont.continuousOn hK
    (mem_univ ⟨τ₀, hτ₀⟩) (mem_univ ⟨τ, hτ⟩)).1 hsurj0 ⟨y, hy⟩
  exact ⟨ι x, hι x, congrArg Subtype.val hx⟩

end TauCeti.CylinderSobolev
