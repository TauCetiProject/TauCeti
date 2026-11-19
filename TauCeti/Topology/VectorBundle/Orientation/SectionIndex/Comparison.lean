/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.SectionIndex.Degree

/-!
# Comparing local indices of sections of two bundles

The local index of a section at an isolated zero depends only on the section read in an oriented
local trivialization: by `TauCeti.VectorBundleOrientation.localHomologyMap_eq_sectionIndex_smul` it
is the local degree of the fibre coordinate. So two sections `s₁` and `s₂` of oriented vector
bundles `E₁` and `E₂` over the same oriented manifold, with the same model fibre, have the same
local index at `z` as soon as, on an open neighbourhood `U` of `z`, they have the same fibre
coordinates in trivializations `e₁` and `e₂` that read the orientations of all fibres over `U` as
one orientation `ω` of the model fibre
(`TauCeti.VectorBundleOrientation.sectionIndex_eq_of_snd_apply_eq`).

This is how local indices are transported between bundles glued from the same local data, for
instance between a line bundle and its point twist away from the twisting point.
-/

public section

noncomputable section

open Bundle Module Set

namespace TauCeti

namespace VectorBundleOrientation

variable {M E' : Type} [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [ChartedSpace E' M] {n : ℕ}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E₁ : M → Type} [TopologicalSpace (TotalSpace F E₁)] [∀ x, AddCommMonoid (E₁ x)]
  [∀ x, Module ℝ (E₁ x)] [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F E₁] [VectorBundle ℝ F E₁]
  {E₂ : M → Type} [TopologicalSpace (TotalSpace F E₂)] [∀ x, AddCommMonoid (E₂ x)]
  [∀ x, Module ℝ (E₂ x)] [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F E₂] [VectorBundle ℝ F E₂]
  (o₁ : VectorBundleOrientation F E₁ (Fin (n + 1)))
  (o₂ : VectorBundleOrientation F E₂ (Fin (n + 1)))
  (hF : finrank ℝ F = n + 1) (oM : HomologicalOrientation M E' (n + 1))
  {s₁ : ∀ x, E₁ x} {s₂ : ∀ x, E₂ x}
  (hs₁ : Continuous fun x ↦ TotalSpace.mk' F x (s₁ x))
  (hs₂ : Continuous fun x ↦ TotalSpace.mk' F x (s₂ x))
  (e₁ : Trivialization F (π F E₁)) [e₁.IsLinear ℝ] (e₂ : Trivialization F (π F E₂)) [e₂.IsLinear ℝ]

/-- **Sections with the same fibre coordinates have the same local index.** Let `s₁` and `s₂` be
sections of oriented vector bundles `E₁` and `E₂` over `M`, with the same model fibre, and let
`e₁` and `e₂` be linear trivializations whose base sets contain an open neighbourhood `U` of `z`
on which `s₁` has no zero other than `z`. If `e₁` and `e₂` read the orientations of all fibres over
`U` as the same orientation `ω` of the model fibre, and `s₁` and `s₂` have the same fibre
coordinates in `e₁` and `e₂` over `U`, then they have the same local index at `z`. -/
theorem sectionIndex_eq_of_snd_apply_eq {z : M} {U : Set M} (hU : IsOpen U) (hz : z ∈ U)
    (hUz : ∀ x ∈ U, s₁ x = 0 → x = z) (hUe₁ : U ⊆ e₁.baseSet) (hUe₂ : U ⊆ e₂.baseSet)
    {ω : Orientation ℝ F (Fin (n + 1))}
    (ho₁ : ∀ x (hx : x ∈ U), e₁.mapOrientation (Fin (n + 1)) (hUe₁ hx) (o₁ x) = ω)
    (ho₂ : ∀ x (hx : x ∈ U), e₂.mapOrientation (Fin (n + 1)) (hUe₂ hx) (o₂ x) = ω)
    (hcoord : ∀ x ∈ U, (e₂ (TotalSpace.mk' F x (s₂ x))).2 = (e₁ (TotalSpace.mk' F x (s₁ x))).2) :
    o₂.sectionIndex hF oM hs₂ z = o₁.sectionIndex hF oM hs₁ z := by
  -- The common fibre coordinate on `U`.
  let σ : C(U, F) := ⟨fun x ↦ (e₁ (TotalSpace.mk' F x.1 (s₁ x.1))).2,
    continuous_snd.comp ((e₁.continuousOn.comp_continuous (hs₁.comp continuous_subtype_val)
      fun x ↦ e₁.mem_source.2 (hUe₁ x.2)))⟩
  have hσ₀ : ∀ x : U, σ x = 0 → s₁ x.1 = 0 := fun x h ↦ by
    by_contra h'
    exact (e₁.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' F x.1 (s₁ x.1)) (hUe₁ x.2)).2 h' h
  have hσz : σ ⁻¹' ({0} : Set F) ⊆ {(⟨z, hz⟩ : U)} := fun x hx ↦
    Subtype.ext (hUz x.1 x.2 (hσ₀ x hx))
  have hUz₂ : ∀ x ∈ U, s₂ x = 0 → x = z := fun x hx h ↦ by
    refine hUz x hx (hσ₀ ⟨x, hx⟩ ?_)
    change (e₁ (TotalSpace.mk' F x (s₁ x))).2 = 0
    rw [← hcoord x hx]
    by_contra h'
    exact (e₂.snd_apply_ne_zero_iff ℝ (v := TotalSpace.mk' F x (s₂ x)) (hUe₂ hx)).1 h' h
  have h₁ := o₁.localHomologyMap_eq_sectionIndex_smul hF oM hs₁ e₁ hU hz hUz hUe₁ ho₁ σ
    (fun _ ↦ rfl) hσz
  have h₂ := o₂.localHomologyMap_eq_sectionIndex_smul hF oM hs₂ e₂ hU hz hUz₂ hUe₂ ho₂ σ
    (fun x ↦ (hcoord x.1 x.2).symm) hσz
  rw [← ω.kronecker_localCohomologyClass_zsmul hF (o₂.sectionIndex hF oM hs₂ z), ← h₂, h₁,
    ω.kronecker_localCohomologyClass_zsmul hF]

end VectorBundleOrientation

end TauCeti
