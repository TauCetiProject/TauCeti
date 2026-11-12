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

The axioms transfer because `f` is a homeomorphism onto its image: the inverse of a
characteristic map on its open cell is continuous because `f` is an embedding, and the weak
topology transfers because `f` is a closed map.

The characteristic map of a cell of the image is the partial equivalence determined by the function
`f ∘ map n i` on the open unit ball, so it depends on nothing else
(`Topology.IsClosedEmbedding.map_relCWComplex_eq_map_relCWComplex`). Thus a cell of `C` which is
also, through a second closed embedding, a cell of another CW complex with the same characteristic
function has literally the same characteristic map in `Y`, as the union of a tower of CW complexes
requires.

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

/-- The characteristic map of a cell of `C`, followed by `f`. It is the partial equivalence
determined by the function `f ∘ map n i` on the open unit ball, so that it depends on nothing else
(`Topology.IsClosedEmbedding.map_relCWComplex_eq_map_relCWComplex`). -/
private def imageCellMap (n : ℕ) (i : cell C n) : PartialEquiv (Fin n → ℝ) Y :=
  (hf.injective.comp_injOn ((map n i).injOn.mono (source_eq n i).ge)).toPartialEquiv
    (f ∘ map n i) (ball 0 1)

private lemma coe_imageCellMap (n : ℕ) (i : cell C n) : ⇑(hf.imageCellMap n i) = f ∘ map n i :=
  rfl

private lemma image_imageCellMap (n : ℕ) (i : cell C n) (S : Set (Fin n → ℝ)) :
    hf.imageCellMap n i '' S = f '' (map n i '' S) := by
  rw [coe_imageCellMap, image_comp]

private lemma source_imageCellMap (n : ℕ) (i : cell C n) :
    (hf.imageCellMap n i).source = ball 0 1 :=
  rfl

private lemma continuousOn_symm_imageCellMap (n : ℕ) (i : cell C n) :
    ContinuousOn (hf.imageCellMap n i).symm (hf.imageCellMap n i).target := by
  have : Nonempty X := ⟨map n i 0⟩
  have hinv : ContinuousOn (invFunOn f univ) (f '' univ) := by
    refine hf.isInducing.continuousOn_iff.2 (continuousOn_id.congr fun y hy ↦ ?_)
    obtain ⟨x, hx, rfl⟩ := hy
    exact invFunOn_eq ⟨x, hx, rfl⟩
  -- On the image of the open ball, the inverse is the inverse of `map n i` after that of `f`.
  refine ((continuousOn_symm n i).comp (hinv.mono ?_) ?_).congr ?_
  · rintro _ ⟨x, -, rfl⟩
    exact mem_image_of_mem f (mem_univ _)
  · rintro _ ⟨x, hx, rfl⟩
    rw [Function.comp_apply, hf.injective.injOn.leftInvOn_invFunOn (mem_univ _)]
    exact (map n i).map_source ((source_eq n i).symm ▸ hx)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← hf.coe_imageCellMap n i, (hf.imageCellMap n i).left_inv hx, Function.comp_apply,
      coe_imageCellMap, Function.comp_apply, hf.injective.injOn.leftInvOn_invFunOn (mem_univ _),
      (map n i).left_inv ((source_eq n i).symm ▸ hx)]

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

omit hC hD in
/-- **The characteristic maps of images depend only on their underlying functions.** Two cells of
images of relative CW complexes under closed embeddings `f` and `g` into the same space have the
same characteristic map, as a partial equivalence, as soon as the characteristic maps of the
original cells followed by `f` and `g` agree as functions. -/
lemma map_relCWComplex_eq_map_relCWComplex {X' : Type u} [TopologicalSpace X'] {g : X' → Y}
    (hg : IsClosedEmbedding g) {E F : Set X'} [RelCWComplex E F] {E' F' : Set Y}
    (hC : f '' C = C') (hD : f '' D = D') (hE : g '' E = E') (hF : g '' F = F') {n : ℕ}
    (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) (j : @cell Y _ E' F' (hg.relCWComplex hE hF) n)
    (h : f ∘ map n (hf.relCWComplexCellEquiv hC hD n i) =
      g ∘ map n (hg.relCWComplexCellEquiv hE hF n j)) :
    @map Y _ C' D' (hf.relCWComplex hC hD) n i = @map Y _ E' F' (hg.relCWComplex hE hF) n j := by
  have hsymm : invFunOn (f ∘ map n (hf.relCWComplexCellEquiv hC hD n i)) (ball 0 1) =
      invFunOn (g ∘ map n (hg.relCWComplexCellEquiv hE hF n j)) (ball 0 1) := by
    rw [h]
  exact PartialEquiv.ext (congrFun h) (congrFun hsymm) rfl

end Topology.IsClosedEmbedding
