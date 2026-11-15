/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties

/-!
# Affine covers with dense total intersection

On a scheme with finitely many irreducible components, every point has an affine
neighbourhood containing all generic points of the components. If the scheme is also
quasi-compact, finitely many such neighbourhoods cover it, and their total intersection
is dense. In particular this applies to Noetherian schemes.

Such covers allow induction by adjoining one compactifiable affine open at a time while
keeping a dense common open. The density here is topological; no reducedness or
scheme-theoretic density is asserted.

The neighbourhood construction takes an affine open around the given point avoiding
the components not containing it, then adjoins disjoint affine neighbourhoods of the
remaining generic points. Affineness of the disjoint union is supplied by Mathlib's
`IsAffineOpen.iSup_of_disjoint` and `IsAffineOpen.sup_of_disjoint`.

## References

* The Stacks Project, Lemma 28.30.4 (tag 01ZX), finding affine neighbourhoods of
  generic points. Here finiteness of all irreducible components permits choosing
  neighbourhoods inside their exclusive loci, without quasi-separatedness.
* The Stacks Project, Theorem 38.33.8 (tag 0F41), the finite affine-cover reduction
  in the Noetherian proof of Nagata compactification.
-/

public section

open TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

/-- For a scheme with finitely many irreducible components, the generic point of a
component has an affine neighbourhood contained in that component and disjoint from
every other component. -/
theorem exists_isAffineOpen_genericPoint_mem_and_disjoint
    (hX : (irreducibleComponents X).Finite) (C : irreducibleComponents X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ (genericPoints.ofComponent C : X) ∈ V ∧
      (V : Set X) ⊆ C.1 ∧
      ∀ D ∈ irreducibleComponents X, D ≠ C.1 → Disjoint (V : Set X) D := by
  let T : Set (Set X) := irreducibleComponents X \ {C.1}
  have hT : T.Finite := hX.sdiff
  let O : X.Opens := ⟨(⋃₀ T)ᶜ, (hT.isClosed_sUnion
    (fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1)).isOpen_compl⟩
  have hOC : (O : Set X) ⊆ C.1 := by
    rw [← closure_sUnion_irreducibleComponents_sdiff_singleton hX C.1 C.2]
    exact subset_closure
  have hηO : (genericPoints.ofComponent C : X) ∈ O := by
    rintro ⟨D, hD, hηD⟩
    have hCD : C.1 ⊆ D :=
      (genericPoints.isGenericPoint_ofComponent C).mem_closed_set_iff
        (isClosed_of_mem_irreducibleComponents D hD.1) |>.mp hηD
    exact hD.2 (Set.mem_singleton_iff.mpr
      (Set.Subset.antisymm (C.2.2 hD.1.1 hCD) hCD))
  obtain ⟨V, hV, hηV, hVO⟩ := exists_isAffineOpen_mem_and_subset hηO
  refine ⟨V, hV, hηV, hVO.trans hOC, fun D hD hDC ↦ ?_⟩
  exact Set.disjoint_left.mpr fun y hyV hyD ↦ hVO hyV ⟨D, ⟨hD, hDC⟩, hyD⟩

/-- On a scheme with finitely many irreducible components, every point has an affine
neighbourhood containing the generic points of all components. -/
theorem exists_isAffineOpen_mem_and_genericPoints_subset
    (hX : (irreducibleComponents X).Finite) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ genericPoints X ⊆ U := by
  classical
  -- Start with an affine neighbourhood avoiding every component not containing x.
  let s : Set (Set X) := {C ∈ irreducibleComponents X | x ∉ C}
  have hs : s.Finite := hX.subset (fun _ hC ↦ hC.1)
  let W₀ : X.Opens := ⟨(⋃₀ s)ᶜ, (hs.isClosed_sUnion
    (fun C hC ↦ isClosed_of_mem_irreducibleComponents C hC.1)).isOpen_compl⟩
  have hxW₀ : x ∈ W₀ := by
    rintro ⟨C, hC, hxC⟩
    exact hC.2 hxC
  obtain ⟨W, hW, hxW, hWW₀⟩ := exists_isAffineOpen_mem_and_subset hxW₀
  -- Each missing generic point has an affine neighbourhood inside its own component
  -- and outside every other component. These neighbourhoods are pairwise disjoint.
  choose V hV hηV hVC hVD using fun C : s ↦
    X.exists_isAffineOpen_genericPoint_mem_and_disjoint hX ⟨C.1, C.2.1⟩
  have : Finite s := hs.to_subtype
  have hpair : Pairwise fun C D : s ↦ Disjoint (V C) (V D) := by
    intro C D hCD
    rw [← Opens.coe_disjoint]
    exact (hVD C D.1 D.2.1 (fun h ↦ hCD (Subtype.ext h.symm))).mono_right (hVC D)
  have hWV : Disjoint W (⨆ C : s, V C) := by
    refine disjoint_iSup_iff.mpr fun C ↦ ?_
    rw [← Opens.coe_disjoint]
    exact Set.disjoint_left.mpr fun y hyW hyV ↦ hWW₀ hyW ⟨C.1, C.2, hVC C hyV⟩
  refine ⟨W ⊔ ⨆ C : s, V C,
    hW.sup_of_disjoint (IsAffineOpen.iSup_of_disjoint hV hpair) hWV,
    Or.inl hxW, ?_⟩
  intro η hη
  let C := genericPoints.component ⟨η, hη⟩
  by_cases hxC : x ∈ (C : Set X)
  · exact Or.inl (((genericPoints.isGenericPoint ⟨η, hη⟩).specializes hxC).mem_open W.isOpen hxW)
  · have hC : C.1 ∈ s := ⟨C.2, hxC⟩
    have heq : (genericPoints.ofComponent ⟨C.1, C.2⟩ : X) = η :=
      congrArg Subtype.val (genericPoints.ofComponent_component ⟨η, hη⟩)
    exact Or.inr (Opens.mem_iSup.mpr ⟨⟨C.1, hC⟩, by
      simpa only [heq] using hηV ⟨C.1, hC⟩⟩)

/-- A quasi-compact scheme with finitely many irreducible components has a finite affine
open cover whose total intersection is dense. This includes every Noetherian scheme. -/
theorem exists_finite_affine_cover_dense_iInter [CompactSpace X]
    (hX : (irreducibleComponents X).Finite) :
    ∃ s : Finset X.affineOpens, (⨆ U ∈ s, U.1) = ⊤ ∧
      Dense (⋂ U ∈ s, (U.1 : Set X)) := by
  classical
  choose U hU hxU hηU using X.exists_isAffineOpen_mem_and_genericPoints_subset hX
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨s.image (fun x ↦ ⟨U x, hU x⟩), ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U y, hU y⟩,
      Opens.mem_iSup.mpr ⟨Finset.mem_image.mpr ⟨y, hys, rfl⟩, hxy⟩⟩
  · apply (dense_iff_closure_eq.mpr (genericPoints.closure (α := X))).mono
    intro η hη
    simp only [Set.mem_iInter]
    intro A hA
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hA
    exact hηU x hη

end AlgebraicGeometry.Scheme
