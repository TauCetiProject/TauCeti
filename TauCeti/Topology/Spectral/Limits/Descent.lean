/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.Limits.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Cofiltered

/-!
# Descent of compact opens and constructible subsets in spectral limits

In a cofiltered limit of spectral spaces with spectral transition maps, every compact open
is the inverse image of a compact open at one stage. The same is true for constructible
subsets. No surjectivity of the transition maps or projections is required.

The compact-open result uses Mathlib's `TopCat.isTopologicalBasis_cofiltered_limit` and
`eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open`: compactness reduces a cover by
finite-stage cylinders to a finite union, and cofilteredness moves that union to one stage.
Boolean induction then gives descent of constructible sets. The compact-open result only
needs compact, prespectral, quasiseparated stages, not sobriety or T₀. These descent results
are useful for presenting spectral spaces by finite spaces and descending finite geometric data.

This extends the compactness argument of Mathlib's
`Profinite.exists_isClopen_of_cofiltered` from profinite spaces to compact opens of spaces
that need not be Hausdorff.

## References

* The Stacks Project, Lemmas 5.24.4 and 5.24.6, Tags 0A2Y and 0A30.
-/

public section

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace TopCat

universe v u w

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
  (F : J ⥤ TopCat.{max v u})
  (hF : ∀ {i j} (f : i ⟶ j), IsSpectralMap (F.map f))
  (c : Cone F) (hc : IsLimit c)

include hF hc

section CompactOpen

variable [∀ j, CompactSpace (F.obj j)] [∀ j, PrespectralSpace (F.obj j)]
  [∀ j, QuasiSeparatedSpace (F.obj j)]

/-- The inverse images of the compact opens at compact prespectral quasiseparated stages
form a basis of a cofiltered limit along spectral maps. -/
theorem isTopologicalBasis_compactOpen_of_isLimit :
    IsTopologicalBasis {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)),
      IsOpen V ∧ IsCompact V ∧ U = c.π.app j ⁻¹' V} := by
  simpa [and_assoc] using isTopologicalBasis_cofiltered_limit.{u, v, w} F c hc
    (fun j ↦ {V : Set (F.obj j) | IsOpen V ∧ IsCompact V})
    (fun _ ↦ PrespectralSpace.isTopologicalBasis)
    (fun _ ↦ ⟨isOpen_univ, isCompact_univ⟩)
    (fun _ _ _ hU hV ↦ ⟨hU.1.inter hV.1, hU.2.inter_of_isOpen hV.2 hU.1 hV.1⟩)
    (fun _ _ f _ hV ↦ ⟨hV.1.preimage (hF f).continuous,
      (hF f).isCompact_preimage_of_isOpen hV.1 hV.2⟩)

/-- Every compact open of a cofiltered limit of compact prespectral quasiseparated spaces
along spectral maps descends to a compact open at one stage. The limiting cone may be any
chosen limit cone. -/
theorem exists_compactOpen_preimage_of_isLimit {U : Set c.pt} (hUo : IsOpen U)
    (hUc : IsCompact U) :
    ∃ (j : J) (V : Set (F.obj j)), IsOpen V ∧ IsCompact V ∧ U = c.π.app j ⁻¹' V := by
  classical
  let B := {U : Set c.pt | ∃ (j : J) (V : Set (F.obj j)),
    IsOpen V ∧ IsCompact V ∧ U = c.π.app j ⁻¹' V}
  have hb : IsTopologicalBasis B := isTopologicalBasis_compactOpen_of_isLimit F hF c hc
  obtain ⟨s, hs, rfl⟩ := eq_finite_iUnion_of_isTopologicalBasis_of_isCompact_open
    (fun V : B ↦ (V : Set c.pt)) (by simpa using hb) U hUc hUo
  clear hUo hUc
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    exact ⟨Classical.choice (IsCofiltered.nonempty (C := J)), ∅,
      isOpen_empty, isCompact_empty, by simp⟩
  | @insert V s _ _ ih =>
    obtain ⟨i, Vi, hVio, hVic, hVi⟩ := V.2
    obtain ⟨j, Wj, hWjo, hWjc, hWj⟩ := ih
    let k := IsCofiltered.min i j
    let a : k ⟶ i := IsCofiltered.minToLeft i j
    let b : k ⟶ j := IsCofiltered.minToRight i j
    refine ⟨k, F.map a ⁻¹' Vi ∪ F.map b ⁻¹' Wj,
      (hVio.preimage (hF a).continuous).union (hWjo.preimage (hF b).continuous),
      ((hF a).isCompact_preimage_of_isOpen hVio hVic).union
        ((hF b).isCompact_preimage_of_isOpen hWjo hWjc), ?_⟩
    simp only [biUnion_insert, preimage_union, hVi, hWj, ← preimage_comp,
      ← coe_comp, c.w]

end CompactOpen

variable [∀ j, SpectralSpace (F.obj j)]

/-- Every constructible subset of a cofiltered spectral limit descends to a constructible
subset at one stage. -/
theorem exists_constructible_preimage_of_isLimit {U : Set c.pt} (hU : IsConstructible U) :
    ∃ (j : J) (V : Set (F.obj j)), IsConstructible V ∧ U = c.π.app j ⁻¹' V := by
  have := spectralSpace_of_isLimit F hF c hc
  induction hU using IsConstructible.empty_union_induction with
  | open_retrocompact U hUo hUc =>
    obtain ⟨j, V, hVo, hVc, hV⟩ :=
      exists_compactOpen_preimage_of_isLimit F hF c hc hUo hUc.isCompact
    exact ⟨j, V, hVc.isConstructible hVo, hV⟩
  | union U hU V hV ihU ihV =>
    obtain ⟨i, Ui, hUi, rfl⟩ := ihU
    obtain ⟨j, Vj, hVj, rfl⟩ := ihV
    let k := IsCofiltered.min i j
    let a : k ⟶ i := IsCofiltered.minToLeft i j
    let b : k ⟶ j := IsCofiltered.minToRight i j
    have hpre {l m : J} (f : l ⟶ m) {W : Set (F.obj m)} (hW : IsConstructible W) :
        IsConstructible (F.map f ⁻¹' W) :=
      hW.preimage (hF f).continuous fun _ hWo hWc ↦
        ((hF f).isCompact_preimage_of_isOpen hWo hWc.isCompact).isRetrocompact
          (hWo.preimage (hF f).continuous)
    refine ⟨k, F.map a ⁻¹' Ui ∪ F.map b ⁻¹' Vj, (hpre a hUi).union (hpre b hVj), ?_⟩
    simp only [preimage_union, ← preimage_comp, ← coe_comp, c.w]
  | compl U hU ih =>
    obtain ⟨j, V, hV, rfl⟩ := ih
    exact ⟨j, Vᶜ, hV.compl, preimage_compl.symm⟩

end TopCat
