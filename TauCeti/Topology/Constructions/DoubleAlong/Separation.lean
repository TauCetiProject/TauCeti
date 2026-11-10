/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.DoubleAlong.Basic
public import TauCeti.Topology.Category.TopCat.OpenEmbedding
public import TauCeti.Topology.Maps.Proper.SecondCountable

/-!
# Separation and countability of a double along a closed subset

For a closed subset, both copies are closed embeddings by the native closed-pushout theorem.
The two unglued parts are disjoint open embeddings. The sum quotient is closed with finite fibres,
hence proper; proper-surjection descent supplies second countability. Hausdorffness has the sharp
criterion: the original space is Hausdorff and the glued subset is closed.

These are topological prerequisites for doubling bordered manifolds. No analytic atlas or
complex-analytic compatibility is asserted here.
-/

public section

open CategoryTheory Limits Topology Set TopologicalSpace

universe u

namespace TauCeti.DoubleAlong

variable {X : Type u} [TopologicalSpace X] (A : Set X)

/-- Closed gluing makes either sheet a closed embedding, without separation assumptions. -/
theorem isClosedEmbedding_inl (hA : IsClosed A) : IsClosedEmbedding (inl A) := by
  rw [inl_eq_pushout_inl]
  exact TauCeti.TopCat.isClosedEmbedding_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A))) hA.isClosedEmbedding_subtypeVal

/-- Closed gluing makes either sheet a closed embedding, without separation assumptions. -/
theorem isClosedEmbedding_inr (hA : IsClosed A) : IsClosedEmbedding (inr A) := by
  rw [inr_eq_pushout_inr]
  exact TauCeti.TopCat.isClosedEmbedding_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A))).flip hA.isClosedEmbedding_subtypeVal

/-- The unglued part of one sheet is exactly the complement of the other sheet. -/
theorem image_compl_inr : inr A '' Aᶜ = (range (inl A))ᶜ := by
  have h := TauCeti.TopCat.image_compl_range_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A)))
  -- The pushout cocone maps are our sheet inclusions; its source map is subtype inclusion.
  simp only [← inl_eq_pushout_inl, ← inr_eq_pushout_inr] at h
  change inr A '' (range (Subtype.val : A → X))ᶜ = (range (inl A))ᶜ at h
  simpa only [Subtype.range_val] using h

/-- The unglued part of one sheet is exactly the complement of the other sheet. -/
theorem image_compl_inl : inl A '' Aᶜ = (range (inr A))ᶜ := by
  have h := TauCeti.TopCat.image_compl_range_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A))).flip
  -- Flipping the same pushout exchanges the two continuous sheet maps.
  simp only [← inl_eq_pushout_inl, ← inr_eq_pushout_inr] at h
  change inl A '' (range (Subtype.val : A → X))ᶜ = (range (inr A))ᶜ at h
  simpa only [Subtype.range_val] using h

/-- The complement of the glued subset is an open embedded part of the first sheet. -/
theorem isOpenEmbedding_inl_compl (hA : IsClosed A) :
    IsOpenEmbedding (Aᶜ.domRestrict (inl A)) := by
  have hclosed : IsClosed (range (Subtype.val : A → X)) := by
    simpa only [Subtype.range_val] using hA
  have h := TauCeti.TopCat.isOpenEmbedding_domRestrict_compl_range_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A))).flip
    hclosed
  -- Unfold the native cocone maps before rewriting the subtype-valued restriction domain.
  simp only [← inl_eq_pushout_inl] at h
  change IsOpenEmbedding ((range (Subtype.val : A → X))ᶜ.domRestrict (inl A)) at h
  rw [Subtype.range_val (s := A)] at h
  exact h

/-- The complement of the glued subset is an open embedded part of the second sheet. -/
theorem isOpenEmbedding_inr_compl (hA : IsClosed A) :
    IsOpenEmbedding (Aᶜ.domRestrict (inr A)) := by
  have hclosed : IsClosed (range (Subtype.val : A → X)) := by
    simpa only [Subtype.range_val] using hA
  have h := TauCeti.TopCat.isOpenEmbedding_domRestrict_compl_range_of_isPushout
    (IsPushout.of_hasPushout (TopCat.ofHom (ContinuousMap.subtypeVal A))
      (TopCat.ofHom (ContinuousMap.subtypeVal A)))
    hclosed
  -- Unfold the native cocone maps before rewriting the subtype-valued restriction domain.
  simp only [← inr_eq_pushout_inr] at h
  change IsOpenEmbedding ((range (Subtype.val : A → X))ᶜ.domRestrict (inr A)) at h
  rw [Subtype.range_val (s := A)] at h
  exact h

/-- The two unglued parts are disjoint. -/
theorem disjoint_image_compl : Disjoint (inl A '' Aᶜ) (inr A '' Aᶜ) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, _, heq⟩
  exact hx ((inl_eq_inr_iff A).1 heq.symm).2

/-- The canonical sum quotient for closed gluing is closed. In general it is not open. -/
theorem isClosedMap_quotientMap (hA : IsClosed A) : IsClosedMap (quotientMap A) := by
  rw [coe_quotientMap]
  exact (isClosedEmbedding_inl A hA).isClosedMap.sumElim (isClosedEmbedding_inr A hA).isClosedMap

/-- Closed gluing gives a proper quotient, with compact finite fibres, without separation axioms. -/
theorem isProperMap_quotientMap (hA : IsClosed A) : IsProperMap (quotientMap A) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨(quotientMap A).continuous, isClosedMap_quotientMap A hA,
      fun z ↦ (finite_fiber_quotientMap A z).isCompact⟩

/-- A double along a closed subset of a second-countable space is second countable. -/
theorem secondCountableTopology [SecondCountableTopology X] (hA : IsClosed A) :
    SecondCountableTopology (DoubleAlong A) :=
  (isProperMap_quotientMap A hA).secondCountableTopology (quotientMap_surjective A)

/-- A double along a closed subset of a Hausdorff space is Hausdorff. -/
theorem t2Space [T2Space X] (hA : IsClosed A) : T2Space (DoubleAlong A) := by
  refine ⟨fun z w hne ↦ ?_⟩
  by_cases hfold : fold A z = fold A w
  · have hsep (x y : X) (hxy : inl A x ≠ inr A y) (h : x = y) :
        ∃ U V : Set (DoubleAlong A), IsOpen U ∧ IsOpen V ∧
          inl A x ∈ U ∧ inr A y ∈ V ∧ Disjoint U V := by
      subst y
      have hx : x ∉ A := fun hx ↦ hxy ((inl_eq_inr_iff A).2 ⟨rfl, hx⟩)
      refine ⟨inl A '' Aᶜ, inr A '' Aᶜ, ?_, ?_, ⟨x, hx, rfl⟩,
        ⟨x, hx, rfl⟩, disjoint_image_compl A⟩
      · rw [image_compl_inl]
        exact (isClosedEmbedding_inr A hA).isClosed_range.isOpen_compl
      · rw [image_compl_inr]
        exact (isClosedEmbedding_inl A hA).isClosed_range.isOpen_compl
    obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := exists_inl_or_inr A z
    · obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := exists_inl_or_inr A w
      · exact (hne (congrArg (inl A) (by simpa using hfold))).elim
      · exact hsep x y hne (by simpa using hfold)
    · obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := exists_inl_or_inr A w
      · obtain ⟨U, V, hU, hV, hy, hx, hUV⟩ :=
          hsep y x (Ne.symm hne) (by simpa using hfold.symm)
        exact ⟨V, U, hV, hU, hx, hy, hUV.symm⟩
      · exact (hne (congrArg (inr A) (by simpa using hfold))).elim
  · obtain ⟨U, V, hU, hV, hz, hw, hUV⟩ := t2_separation hfold
    exact ⟨fold A ⁻¹' U, fold A ⁻¹' V, hU.preimage (fold A).continuous,
      hV.preimage (fold A).continuous, hz, hw, hUV.preimage _⟩

/-- Hausdorffness requires exactly a Hausdorff original space and a closed glued subset. -/
theorem t2Space_iff : T2Space (DoubleAlong A) ↔ T2Space X ∧ IsClosed A := by
  constructor
  · intro h
    let := h
    refine ⟨(isEmbedding_inl A).t2Space, ?_⟩
    convert isClosed_eq (inl A).continuous (inr A).continuous using 1
    ext x
    simp
  · rintro ⟨hX, hA⟩
    let := hX
    exact t2Space A hA

end TauCeti.DoubleAlong
