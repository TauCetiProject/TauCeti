/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# The image of a CW complex under a closed embedding

Let `f : X → Y` be a closed embedding and let `C` be a CW complex relative to `D` in `X`. Then
`f '' C` is a CW complex relative to `f '' D` in `Y`
(`Topology.IsClosedEmbedding.relCWComplex`), with the same cells
(`Topology.IsClosedEmbedding.relCWComplexCellEquiv`) and the characteristic maps of `C` followed by
`f` (`Topology.IsClosedEmbedding.coe_map_relCWComplex`). For an absolute CW complex, the base is
`f '' ∅ = ∅`, and `Topology.RelCWComplex.toCWComplex` turns the result into an absolute CW
complex.

This is how a CW structure on a space `X` is read inside a larger space containing `X` as a
closed subspace, for instance the target of a relative CW complex built on `X`, where it serves
as the base. The images are given as sets `C'` and `D'` with equations `f '' C = C'` and
`f '' D = D'`, because the base of a relative CW complex is determined by the complex, and the
image of `Set.univ` is the range of `f` only up to `Set.image_univ`.

The two spaces lie in a common universe, since the cells of a CW complex are indexed by types in
the universe of its ambient space.

The characteristic maps of a CW structure can also be replaced by other partial equivalences with
the same values and sources (`Topology.RelCWComplex.replaceMap`), for instance by the canonical
partial equivalences `Set.InjOn.toPartialEquiv` determined by their values. Two CW structures whose
characteristic maps agree as functions then have literally the same characteristic maps.

The axioms transfer because `f` is a homeomorphism onto its image: the inverse of a
characteristic map on its open cell is continuous because `f` is an embedding, and the weak
topology transfers because `f` is a closed map.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and the Appendix, for CW complexes and their subcomplexes as closed subspaces.
-/

public section

noncomputable section

open Function Metric Set Topology Topology.RelCWComplex

namespace Topology.IsClosedEmbedding

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
  (hf : IsClosedEmbedding f) {C D : Set X} [RelCWComplex C D] {C' D' : Set Y}

/-- The characteristic map of a cell of `C`, followed by `f`. -/
private def imageCellMap (n : ℕ) (i : cell C n) : PartialEquiv (Fin n → ℝ) Y :=
  haveI : Nonempty X := ⟨map n i 0⟩
  (map n i).trans (hf.injective.injOn.toPartialEquiv f univ)

private lemma coe_imageCellMap (n : ℕ) (i : cell C n) : ⇑(hf.imageCellMap n i) = f ∘ map n i :=
  rfl

private lemma image_imageCellMap (n : ℕ) (i : cell C n) (S : Set (Fin n → ℝ)) :
    hf.imageCellMap n i '' S = f '' (map n i '' S) := by
  rw [coe_imageCellMap, image_comp]

private lemma source_imageCellMap (n : ℕ) (i : cell C n) :
    (hf.imageCellMap n i).source = ball 0 1 := by
  have : Nonempty X := ⟨map n i 0⟩
  simp [imageCellMap, source_eq]

private lemma continuousOn_symm_imageCellMap (n : ℕ) (i : cell C n) :
    ContinuousOn (hf.imageCellMap n i).symm (hf.imageCellMap n i).target := by
  have : Nonempty X := ⟨map n i 0⟩
  have hinv : ContinuousOn (invFunOn f univ) (f '' univ) := by
    refine hf.isInducing.continuousOn_iff.2 (continuousOn_id.congr fun y hy ↦ ?_)
    obtain ⟨x, hx, rfl⟩ := hy
    exact invFunOn_eq ⟨x, hx, rfl⟩
  rw [imageCellMap, PartialEquiv.coe_trans_symm, PartialEquiv.trans_target]
  exact (continuousOn_symm n i).comp (hinv.mono inter_subset_left) fun y hy ↦ hy.2

/-- **The image of a relative CW complex under a closed embedding.** If `f` is a closed embedding
and `C` is a CW complex relative to `D`, then `C' = f '' C` is a CW complex relative to
`D' = f '' D`, with the cells of `C` and their characteristic maps followed by `f`. -/
@[instance_reducible]
def relCWComplex (hC : f '' C = C') (hD : f '' D = D') : RelCWComplex C' D' where
  cell := cell C
  map := hf.imageCellMap
  source_eq := hf.source_imageCellMap
  continuousOn n i := hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n i)
  continuousOn_symm := hf.continuousOn_symm_imageCellMap
  pairwiseDisjoint' := by
    rintro ⟨n, i⟩ - ⟨m, j⟩ - hne
    simp only [Function.onFun, image_imageCellMap]
    exact (disjoint_image_iff hf.injective).2 (pairwiseDisjoint (C := C) (mem_univ _)
      (mem_univ _) hne)
  disjointBase' n i := by
    rw [image_imageCellMap, ← hD]
    exact (disjoint_image_iff hf.injective).2 (disjointBase n i)
  mapsTo n i := by
    obtain ⟨I, hI⟩ := RelCWComplex.mapsTo n i
    refine ⟨I, ?_⟩
    simp only [image_imageCellMap]
    rw [coe_imageCellMap, ← hD]
    simpa only [image_union, image_iUnion₂] using (mapsTo_image f _).comp hI
  closed' A hAC hA := by
    have hAf : A ⊆ range f := hAC.trans (hC ▸ image_subset_range f C)
    have hpre (S : Set X) : f ⁻¹' A ∩ S = f ⁻¹' (A ∩ f '' S) := by
      rw [preimage_inter, preimage_image_eq _ hf.injective]
    rw [← image_preimage_eq_of_subset hAf]
    refine hf.isClosedMap _
      (RelCWComplex.closed' (C := C) (f ⁻¹' A) (fun x hx ↦ ?_) ⟨fun n j ↦ ?_, ?_⟩)
    · obtain ⟨y, hy, hyx⟩ := hC ▸ hAC hx
      exact hf.injective hyx ▸ hy
    · rw [hpre, ← image_imageCellMap]
      exact (hA.1 n j).preimage hf.continuous
    · rw [hpre, hD]
      exact hA.2.preimage hf.continuous
  isClosedBase := hD ▸ hf.isClosedMap _ (isClosedBase C)
  union' := by
    have := congrArg (f '' ·) (RelCWComplex.union (C := C))
    simp only [image_union, image_iUnion, closedCell] at this
    simpa only [image_imageCellMap, hC, hD] using this

variable (hC : f '' C = C') (hD : f '' D = D')

/-- The cells of the image of `C` under a closed embedding are the cells of `C`. -/
def relCWComplexCellEquiv (n : ℕ) : @cell Y _ C' D' (hf.relCWComplex hC hD) n ≃ cell C n :=
  Equiv.refl _

/-- The characteristic maps of the image of `C` under a closed embedding `f` are those of `C`
followed by `f`. -/
@[simp]
lemma coe_map_relCWComplex (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) :
    ⇑(@map Y _ C' D' (hf.relCWComplex hC hD) n i) =
      f ∘ map n (hf.relCWComplexCellEquiv hC hD n i) :=
  (rfl)

/-- The open cells of the image of `C` under `f` are the images of the open cells of `C`. -/
@[simp]
lemma openCell_relCWComplex (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) :
    @openCell Y _ C' D' (hf.relCWComplex hC hD) n i =
      f '' openCell n (hf.relCWComplexCellEquiv hC hD n i) :=
  hf.image_imageCellMap n _ _

/-- The closed cells of the image of `C` under `f` are the images of the closed cells of `C`. -/
@[simp]
lemma closedCell_relCWComplex (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) :
    @closedCell Y _ C' D' (hf.relCWComplex hC hD) n i =
      f '' closedCell n (hf.relCWComplexCellEquiv hC hD n i) :=
  hf.image_imageCellMap n _ _

/-- The boundaries of the cells of the image of `C` under `f` are the images of the boundaries of
the cells of `C`. -/
@[simp]
lemma cellFrontier_relCWComplex (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) :
    @cellFrontier Y _ C' D' (hf.relCWComplex hC hD) n i =
      f '' cellFrontier n (hf.relCWComplexCellEquiv hC hD n i) :=
  hf.image_imageCellMap n _ _

end Topology.IsClosedEmbedding

namespace Topology.RelCWComplex

universe u

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D]

/-- The CW structure on `C` relative to `D` with the cells of a given one, whose characteristic
maps are replaced by partial equivalences `φ n i` with the same values and the same sources. Such a
partial equivalence has the same image of the source, and its inverse agrees there with the old
one, so all the axioms transfer. This is used to make characteristic maps depend only on their
values, for instance through `Set.InjOn.toPartialEquiv`. -/
@[instance_reducible]
def replaceMap (φ : ∀ n, cell C n → PartialEquiv (Fin n → ℝ) X)
    (hφ : ∀ n i, ⇑(φ n i) = map n i) (hsource : ∀ n i, (φ n i).source = (map n i).source) :
    RelCWComplex C D where
  cell := cell C
  map := φ
  source_eq n i := (hsource n i).trans (source_eq n i)
  continuousOn n i := hφ n i ▸ RelCWComplex.continuousOn n i
  continuousOn_symm n i := by
    have htarget : (φ n i).target = (map n i).target := by
      rw [← (φ n i).image_source_eq_target, ← (map n i).image_source_eq_target, hφ, hsource]
    rw [htarget]
    refine (RelCWComplex.continuousOn_symm n i).congr fun y hy ↦ ?_
    rw [← (map n i).image_source_eq_target] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [(map n i).left_inv hx, ← hφ, (φ n i).left_inv (hsource n i ▸ hx)]
  pairwiseDisjoint' := by
    simpa only [hφ] using RelCWComplex.pairwiseDisjoint' (C := C) (D := D)
  disjointBase' n i := by
    simpa only [hφ] using RelCWComplex.disjointBase' (C := C) n i
  mapsTo n i := by
    simpa only [hφ] using RelCWComplex.mapsTo (C := C) n i
  closed' A hAC hA := RelCWComplex.closed' (C := C) A hAC (by simpa only [hφ] using hA)
  isClosedBase := isClosedBase C
  union' := by
    simpa only [hφ] using RelCWComplex.union' (C := C) (D := D)

variable (φ : ∀ n, cell C n → PartialEquiv (Fin n → ℝ) X) (hφ : ∀ n i, ⇑(φ n i) = map n i)
  (hsource : ∀ n i, (φ n i).source = (map n i).source)

/-- The cells of `Topology.RelCWComplex.replaceMap` are the cells of the original structure. -/
def replaceMapCellEquiv (n : ℕ) : @cell X _ C D (replaceMap φ hφ hsource) n ≃ cell C n :=
  Equiv.refl _

/-- The characteristic maps of `Topology.RelCWComplex.replaceMap` are the given partial
equivalences. -/
lemma map_replaceMap (n : ℕ) (i : @cell X _ C D (replaceMap φ hφ hsource) n) :
    @map X _ C D (replaceMap φ hφ hsource) n i = φ n (replaceMapCellEquiv φ hφ hsource n i) :=
  (rfl)

end Topology.RelCWComplex
