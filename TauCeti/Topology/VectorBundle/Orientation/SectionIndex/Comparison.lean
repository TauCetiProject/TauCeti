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
`e₁` and `e₂` be linear trivializations whose base sets contain an open neighbourhood `U` of `z`.
If `e₁` and `e₂` read the orientations of all fibres over `U` as the same orientation `ω` of the
model fibre, and `s₁` and `s₂` have the same fibre coordinates in `e₁` and `e₂` over `U`, then they
have the same local index at `z`. -/
theorem sectionIndex_eq_of_snd_apply_eq {z : M} {U : Set M} (hU : IsOpen U) (hz : z ∈ U)
    (hUe₁ : U ⊆ e₁.baseSet) (hUe₂ : U ⊆ e₂.baseSet) {ω : Orientation ℝ F (Fin (n + 1))}
    (ho₁ : ∀ x (hx : x ∈ U), e₁.mapOrientation (Fin (n + 1)) (hUe₁ hx) (o₁ x) = ω)
    (ho₂ : ∀ x (hx : x ∈ U), e₂.mapOrientation (Fin (n + 1)) (hUe₂ hx) (o₂ x) = ω)
    (hcoord : ∀ x ∈ U, (e₂ (TotalSpace.mk' F x (s₂ x))).2 = (e₁ (TotalSpace.mk' F x (s₁ x))).2) :
    o₂.sectionIndex hF oM hs₂ z = o₁.sectionIndex hF oM hs₁ z := by
  -- On `U` the two sections vanish at the same points.
  have hzero : ∀ x ∈ U, s₂ x = 0 ↔ s₁ x = 0 := fun x hx ↦ by
    rw [← e₂.snd_apply_eq_zero_iff ℝ (v := TotalSpace.mk' F x (s₂ x)) (hUe₂ hx),
      ← e₁.snd_apply_eq_zero_iff ℝ (v := TotalSpace.mk' F x (s₁ x)) (hUe₁ hx), hcoord x hx]
  by_cases hiso : ∃ V, IsOpen V ∧ z ∈ V ∧ ∀ x ∈ V, s₁ x = 0 → x = z
  swap
  · -- If `z` is not an isolated zero of `s₁`, it is not one of `s₂` either: both indices are `0`.
    have hiso₂ : ¬ ∃ V, IsOpen V ∧ z ∈ V ∧ ∀ x ∈ V, s₂ x = 0 → x = z := by
      rintro ⟨V, hV, hzV, hVz⟩
      exact hiso ⟨V ∩ U, hV.inter hU, ⟨hzV, hz⟩, fun x hx h ↦ hVz x hx.1 ((hzero x hx.2).2 h)⟩
    rw [sectionIndex_of_not_isolated _ _ _ _ hiso₂, sectionIndex_of_not_isolated _ _ _ _ hiso]
  -- Shrink `U` to `V ∩ U`, which contains no zero of `s₁`, nor of `s₂`, other than `z`.
  obtain ⟨V, hV, hzV, hVz⟩ := hiso
  have hW : IsOpen (V ∩ U) := hV.inter hU
  have hzW : z ∈ V ∩ U := ⟨hzV, hz⟩
  have hWe₁ : V ∩ U ⊆ e₁.baseSet := fun x hx ↦ hUe₁ hx.2
  have hWe₂ : V ∩ U ⊆ e₂.baseSet := fun x hx ↦ hUe₂ hx.2
  have hWz₂ : ∀ x ∈ V ∩ U, s₂ x = 0 → x = z := fun x hx h ↦ hVz x hx.1 ((hzero x hx.2).1 h)
  -- The common fibre coordinate on `V ∩ U`.
  let σ := fiberCoord hs₁ e₁ hWe₁
  have hσz := fiberCoord_preimage_subset hs₁ e₁ hzW (fun x hx ↦ hVz x hx.1) hWe₁
  have h₁ := o₁.localHomologyMap_eq_sectionIndex_smul hF oM hs₁ e₁ hW hzW
    (fun x hx ↦ hVz x hx.1) hWe₁ (fun x hx ↦ ho₁ x hx.2) σ
    (fun x ↦ fiberCoord_apply hs₁ e₁ hWe₁ x) hσz
  have h₂ := o₂.localHomologyMap_eq_sectionIndex_smul hF oM hs₂ e₂ hW hzW hWz₂ hWe₂
    (fun x hx ↦ ho₂ x hx.2) σ (fun x ↦ (fiberCoord_apply hs₁ e₁ hWe₁ x).trans
      (hcoord x.val x.property.2).symm) hσz
  rw [← ω.kronecker_localCohomologyClass_zsmul hF (o₂.sectionIndex hF oM hs₂ z), ← h₂, h₁,
    ω.kronecker_localCohomologyClass_zsmul hF]

end VectorBundleOrientation

end TauCeti
