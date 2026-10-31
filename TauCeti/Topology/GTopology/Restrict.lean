/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.GTopology.ContinuousMap

/-!
# The G-topology induced on an admissible open

Let `G` be a G-topology on `X` and `U` an admissible open. The induced G-topology
`GTopology.restrict G U` on the underlying set `ι U` has as admissible opens the admissible opens
of `G` contained in `U`, and as admissible covers the admissible covers of `G` among them
[BGR, §9.1.1]. Its admissible opens are indexed by `Set.Iic U`; as subsets of `ι U` they are
exactly the subsets whose image in `X` is admissible (`GTopology.mem_range_restrictEmbedding_iff`).

The inclusion of `ι U` into `X` is a continuous map of G-topologies
(`GTopology.restrictInclusion`), through which every continuous map with image in `ι U` factors
uniquely (`GTopology.ContinuousMap.codRestrict`). The induced G-topology satisfies (G0)–(G2)
whenever `G` does (`GTopology.Saturated.restrict`). On the G-topology of ordinary open
covers, restriction to an open subset gives the open subsets and open covers of the subspace.

The inclusion functor of `Set.Iic U` into the admissible opens of `G` is a continuous functor of
sites (`GTopology.isContinuous_iicFunctor`), so Mathlib's
`Functor.sheafPushforwardContinuous` restricts sheaves on `G` to sheaves on the induced
G-topology of `U`. This is the restriction `F|U` of a sheaf to an admissible open used to define
G-ringed spaces and their open subspaces.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§9.1.1 and 9.3.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

namespace GTopology

variable {X : Type u} {B : Type v} [SemilatticeInf B] [OrderTop B] {ι : B ↪o Set X}

section Embedding

omit [OrderTop B]

variable (ι) in
/-- The admissible opens contained in `U`, as subsets of `ι U`: an admissible open `V ≤ U` is
sent to its underlying set `ι V`, viewed inside `ι U`. -/
def restrictEmbedding (U : B) : Set.Iic U ↪o Set (ι U) :=
  .ofMapLEIff (fun V ↦ (↑) ⁻¹' ι V) fun V W ↦ by
    rw [Subtype.preimage_val_subset_preimage_val_iff, Set.inter_eq_right.mpr (ι.monotone V.2),
      Set.inter_eq_right.mpr (ι.monotone W.2), ι.le_iff_le, Subtype.coe_le_coe]

@[simp]
theorem restrictEmbedding_apply (U : B) (V : Set.Iic U) :
    restrictEmbedding ι U V = (↑) ⁻¹' ι V := (rfl)

/-- The image in `X` of an admissible open of `ι U` is its underlying admissible open. -/
theorem image_restrictEmbedding (U : B) (V : Set.Iic U) :
    (↑) '' restrictEmbedding ι U V = ι V := by
  rw [restrictEmbedding_apply, Subtype.image_preimage_coe,
    Set.inter_eq_right.mpr (ι.monotone V.2)]

/-- A subset of `ι U` is an admissible open of the induced G-topology exactly when its image in
`X` is an admissible open. -/
theorem mem_range_restrictEmbedding_iff {U : B} {V : Set (ι U)} :
    V ∈ Set.range (restrictEmbedding ι U) ↔ (↑) '' V ∈ Set.range ι := by
  refine ⟨fun ⟨W, hW⟩ ↦ ⟨W, by rw [← hW, image_restrictEmbedding]⟩, fun ⟨W, hW⟩ ↦ ?_⟩
  have hWU : W ≤ U := ι.le_iff_le.mp (hW ▸ Subtype.coe_image_subset _ V)
  exact ⟨⟨W, hWU⟩, by
    rw [restrictEmbedding_apply, hW, Set.preimage_image_eq _ Subtype.val_injective]⟩

end Embedding

variable (G : GTopology ι)

/-- The G-topology induced on an admissible open `U` [BGR, §9.1.1]: its admissible opens are the
admissible opens of `G` contained in `U`, and a family of them is an admissible cover exactly when
it is an admissible cover for `G`. -/
def restrict (U : B) : GTopology (restrictEmbedding ι U) where
  map_top := by simp
  map_inf V W := by simp [G.map_inf]
  Covers V S := G.Covers V ((↑) '' S)
  subset {V S} h W hW := Subtype.coe_le_coe.mp (G.subset h W ⟨W, hW, rfl⟩)
  union_eq {V S} h := by
    rw [restrictEmbedding_apply, ← G.union_eq h]
    simp [Set.preimage_iUnion]
  identity V := by simpa only [Set.image_singleton] using G.identity V
  restriction {V S} h W hWV := by
    simpa only [Set.image_image, Set.Iic.coe_inf] using G.restriction h W hWV
  transitive {V S T} h hT := by
    -- Extend `T` to all admissible opens of `G` by sending `W` to the cover of `W ⊓ U`.
    let T' (W : B) : Set B := (↑) '' T ⟨W ⊓ U, inf_le_right⟩
    have hT' (W : Set.Iic U) : T' W = (↑) '' T W := by
      simp only [T', inf_eq_left.mpr W.2]
    have h' := G.transitive (T := T') h (by
      rintro _ ⟨W, hW, rfl⟩
      rw [hT']
      exact hT W hW)
    simpa only [Set.biUnion_image, hT', Set.image_iUnion₂] using h'

/-- The admissible covers of the G-topology induced on `U` are the admissible covers of `G`. -/
@[simp]
theorem restrict_covers_iff {U : B} {V : Set.Iic U} {S : Set (Set.Iic U)} :
    (G.restrict U).Covers V S ↔ G.Covers V ((↑) '' S) :=
  Iff.rfl

/-- The inclusion of an admissible open `U` into `X` is a continuous map of G-topologies from the
induced G-topology on `U`. The preimage of an admissible open `V` is `V ⊓ U`. -/
def restrictInclusion (U : B) : (G.restrict U).ContinuousMap G where
  toFun := (↑)
  comap V := ⟨V ⊓ U, inf_le_right⟩
  coe_comap' V := by
    rw [restrictEmbedding_apply, G.map_inf, Subtype.preimage_coe_inter_self]
  covers_comap {V S} h := by
    rw [restrict_covers_iff, Set.image_image]
    have h' := G.restriction h (V ⊓ U) inf_le_left
    refine Set.image_congr (fun W hW ↦ ?_) ▸ h'
    simp only [← inf_assoc, inf_eq_left.mpr (G.subset h W hW)]

@[simp]
theorem coe_restrictInclusion (U : B) : ⇑(G.restrictInclusion U) = (↑) := (rfl)

@[simp]
theorem coe_restrictInclusion_comap (U : B) (V : B) :
    ((G.restrictInclusion U).comap V : B) = V ⊓ U := (rfl)

namespace ContinuousMap

variable {G} {Y : Type*} {B' : Type*} [SemilatticeInf B'] [OrderTop B'] {ι' : B' ↪o Set Y}
  {G' : GTopology ι'}

/-- A continuous map of G-topologies with image in an admissible open `U` is a continuous map to
the G-topology induced on `U`. -/
def codRestrict (f : G'.ContinuousMap G) {U : B} (hf : ∀ y, f y ∈ ι U) :
    G'.ContinuousMap (G.restrict U) where
  toFun y := ⟨f y, hf y⟩
  comap V := f.comap V
  coe_comap' V := by
    ext y
    simp [coe_comap]
  covers_comap {V S} h := by
    simpa only [Set.image_image] using f.covers_comap h

@[simp]
theorem coe_codRestrict_apply (f : G'.ContinuousMap G) {U : B} (hf : ∀ y, f y ∈ ι U) (y : Y) :
    (f.codRestrict hf y : X) = f y := (rfl)

@[simp]
theorem codRestrict_comap (f : G'.ContinuousMap G) {U : B} (hf : ∀ y, f y ∈ ι U)
    (V : Set.Iic U) : (f.codRestrict hf).comap V = f.comap V := (rfl)

/-- A continuous map with image in `U` factors through the inclusion of `U`. -/
@[simp]
theorem restrictInclusion_comp_codRestrict (f : G'.ContinuousMap G) {U : B}
    (hf : ∀ y, f y ∈ ι U) : (G.restrictInclusion U).comp (f.codRestrict hf) = f :=
  ext fun _ ↦ by simp

/-- A continuous map to the G-topology induced on `U` is the corestriction of its composition
with the inclusion of `U`. -/
@[simp]
theorem codRestrict_restrictInclusion_comp {U : B} (g : G'.ContinuousMap (G.restrict U)) :
    ((G.restrictInclusion U).comp g).codRestrict (fun y ↦ by simp) = g :=
  ext fun _ ↦ Subtype.ext (by simp)

end ContinuousMap

/-- The G-topology induced on an admissible open satisfies (G0)–(G2) whenever `G` does. -/
theorem Saturated.restrict {G : GTopology ι} (hG : G.Saturated) (U : B) :
    (G.restrict U).Saturated where
  empty_mem_range := by
    rw [mem_range_restrictEmbedding_iff, Set.image_empty]
    exact hG.empty_mem_range
  mem_range_of_covers {V S} h V' hV' hS := by
    simp only [mem_range_restrictEmbedding_iff] at hS ⊢
    refine hG.mem_range_of_covers h _ ?_ ?_
    · simpa only [image_restrictEmbedding] using Set.image_mono (f := Subtype.val) hV'
    · rintro _ ⟨W, hW, rfl⟩
      simpa only [Set.image_inter Subtype.val_injective, image_restrictEmbedding] using hS W hW
  covers_of_refinement {V S R} hS hR hRS := by
    rw [restrict_covers_iff] at hR ⊢
    refine hG.covers_of_refinement ?_ hR ?_
    · rw [← image_restrictEmbedding, ← hS, Set.image_sUnion, Set.image_image, Set.image_image]
      simp only [image_restrictEmbedding]
    · rintro _ ⟨W, hW, rfl⟩
      obtain ⟨W', hW', hWW'⟩ := hRS W hW
      exact ⟨W', ⟨W', hW', rfl⟩, hWW'⟩

section Site

/-- The inclusion of the admissible opens contained in `U` into the admissible opens of `G`. -/
abbrev iicFunctor (U : B) : Set.Iic U ⥤ B :=
  (OrderEmbedding.subtype (· ∈ Set.Iic U)).monotone.functor

/-- The inclusion functor of `Set.Iic U` sends admissible covers of the induced G-topology to
admissible covers of `G`. -/
theorem coverPreserving_iicFunctor (U : B) :
    CoverPreserving (G.restrict U).grothendieckTopology G.grothendieckTopology
      (iicFunctor U) :=
  coverPreserving_functor _ fun hS ↦ hS

/-- The inclusion functor of `Set.Iic U` is a continuous functor of sites, so
`Functor.sheafPushforwardContinuous` restricts sheaves on `G` to sheaves on the G-topology
induced on `U`. -/
instance isContinuous_iicFunctor (U : B) :
    (iicFunctor U).IsContinuous (G.restrict U).grothendieckTopology G.grothendieckTopology :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfDownwardsClosed (F := iicFunctor U) _ fun {V W} g ↦
      ⟨⟨W, (leOfHom g).trans V.2⟩, Iso.refl _⟩)
    (G.coverPreserving_iicFunctor U)

end Site

section Topological

open TopologicalSpace

variable {Y : Type u} [TopologicalSpace Y]

/-- The admissible opens of the G-topology induced on an open subset `U` by the G-topology of
ordinary open covers are the open subsets of the subspace `U`. -/
theorem range_restrictEmbedding_opensEmbedding (U : Opens Y) :
    Set.range (restrictEmbedding (opensEmbedding Y) U) = {V | IsOpen V} := by
  have hU : IsOpen (opensEmbedding Y U) := by
    rw [opensEmbedding_apply]
    exact U.isOpen
  ext V
  refine mem_range_restrictEmbedding_iff.trans ⟨fun ⟨W, hW⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [opensEmbedding_apply] at hW
    exact hU.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mpr (hW ▸ W.isOpen)
  · exact ⟨⟨Subtype.val '' V, hU.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen.mp h⟩,
      opensEmbedding_apply Y _⟩

/-- The admissible covers of the G-topology induced on an open subset `U` by the G-topology of
ordinary open covers are the ordinary open covers in the subspace `U`. -/
theorem restrict_topological_covers_iff {U : Opens Y} {V : Set.Iic U} {S : Set (Set.Iic U)} :
    ((topological Y).restrict U).Covers V S ↔
      ⋃₀ (restrictEmbedding (opensEmbedding Y) U '' S) =
        restrictEmbedding (opensEmbedding Y) U V := by
  refine ⟨((topological Y).restrict U).union_eq, fun h ↦ ?_⟩
  rw [restrict_covers_iff, topological_covers_iff, ← opensEmbedding_apply,
    ← image_restrictEmbedding, ← h, Set.image_sUnion]
  simp only [Set.image_image, image_restrictEmbedding, opensEmbedding_apply]

end Topological

end GTopology

end TauCeti
