/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# Extending and pushing forward relative CW complexes along embeddings

Let `f : X → Y` be an embedding and let `C` be a CW complex relative to `D` in `X`.

* When `f` is a closed embedding, `f '' C` is a CW complex relative to `f '' D` in `Y`
  (`Topology.IsClosedEmbedding.relCWComplex`), with the same cells
  (`Topology.IsClosedEmbedding.relCWComplexCellEquiv`) and the characteristic maps of `C` followed
  by `f` (`Topology.IsClosedEmbedding.coe_map_relCWComplex`). For an absolute CW complex, the base
  is `f '' ∅ = ∅`, and `Topology.RelCWComplex.toCWComplex` turns the result into an absolute CW
  complex.
* When `f` is an open embedding, `f` need not be a closed map, so `f '' C` alone need not carry the
  weak topology in `Y` when cells accumulate outside `range f`. If, however, `D'` is a closed subset
  of `Y` whose preimage `f ⁻¹' D'` is `D` and whose interior contains `(range f)ᶜ`, then
  `C' = D' ∪ f '' C` is a CW complex relative to `D'` in `Y`
  (`Topology.IsOpenEmbedding.relCWComplex`), with the same cells
  (`Topology.IsOpenEmbedding.relCWComplexCellEquiv`), characteristic maps `f ∘ map n i`, and
  finiteness properties (`Topology.IsOpenEmbedding.finiteDimensional_relCWComplex`,
  `Topology.IsOpenEmbedding.finiteType_relCWComplex`, and
  `Topology.IsOpenEmbedding.finite_relCWComplex`).
  In the open-embedding case, `{range f, interior D'}` is an open cover of `Y`: on `interior D'`
  closedness relative to `C'` reduces to intersection with `D'`, and on `range f` the open embedding
  identifies closed sets with those of `X` where the weak topology of `C` applies.

In both cases the two spaces lie in a common universe, since the cells of a CW complex are indexed
by types in the universe of its ambient space.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and the Appendix, for CW complexes, relative CW complexes, and the weak topology.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Section 7.
-/

public section

noncomputable section

open Function Metric Set Topology Topology.RelCWComplex

universe u

namespace Topology.IsEmbedding

section Map

variable {X Y : Type u} [TopologicalSpace X] {f : X → Y} {C D : Set X} [RelCWComplex C D]

/-- The characteristic map of a cell of `C`, followed by an injective map `f`. -/
private def imageCellMap (hinj : Injective f) (n : ℕ) (i : cell C n) :
    PartialEquiv (Fin n → ℝ) Y :=
  haveI : Nonempty X := ⟨map n i 0⟩
  (map n i).trans (hinj.injOn.toPartialEquiv f univ)

private lemma coe_imageCellMap (hinj : Injective f) (n : ℕ) (i : cell C n) :
    ⇑(imageCellMap hinj n i) = f ∘ map n i :=
  rfl

private lemma image_imageCellMap (hinj : Injective f) (n : ℕ) (i : cell C n)
    (S : Set (Fin n → ℝ)) : imageCellMap hinj n i '' S = f '' (map n i '' S) := by
  rw [coe_imageCellMap, image_comp]

private lemma source_imageCellMap (hinj : Injective f) (n : ℕ) (i : cell C n) :
    (imageCellMap hinj n i).source = ball 0 1 := by
  have : Nonempty X := ⟨map n i 0⟩
  simp [imageCellMap, source_eq]

end Map

private lemma continuousOn_symm_imageCellMap {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) {C D : Set X} [RelCWComplex C D]
    (n : ℕ) (i : cell C n) :
    ContinuousOn (imageCellMap hf.injective n i).symm (imageCellMap hf.injective n i).target := by
  have : Nonempty X := ⟨map n i 0⟩
  have hinv : ContinuousOn (invFunOn f univ) (f '' univ) := by
    refine hf.isInducing.continuousOn_iff.2 (continuousOn_id.congr fun y hy ↦ ?_)
    obtain ⟨x, hx, rfl⟩ := hy
    exact invFunOn_eq ⟨x, hx, rfl⟩
  rw [imageCellMap, PartialEquiv.coe_trans_symm, PartialEquiv.trans_target]
  exact (continuousOn_symm n i).comp (hinv.mono inter_subset_left) fun y hy ↦ hy.2

end Topology.IsEmbedding

namespace Topology.IsClosedEmbedding

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
  (hf : IsClosedEmbedding f) {C D : Set X} [RelCWComplex C D] {C' D' : Set Y}

/-- **The image of a relative CW complex under a closed embedding.** If `f` is a closed embedding
and `C` is a CW complex relative to `D`, then `C' = f '' C` is a CW complex relative to
`D' = f '' D`, with the cells of `C` and their characteristic maps followed by `f`. -/
@[instance_reducible]
def relCWComplex (hC : f '' C = C') (hD : f '' D = D') : RelCWComplex C' D' where
  cell := cell C
  map := IsEmbedding.imageCellMap hf.injective
  source_eq := IsEmbedding.source_imageCellMap hf.injective
  continuousOn n i := hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n i)
  continuousOn_symm := IsEmbedding.continuousOn_symm_imageCellMap hf.isEmbedding
  pairwiseDisjoint' := by
    rintro ⟨n, i⟩ - ⟨m, j⟩ - hne
    simp only [Function.onFun, IsEmbedding.image_imageCellMap]
    exact (disjoint_image_iff hf.injective).2 (pairwiseDisjoint (C := C) (mem_univ _)
      (mem_univ _) hne)
  disjointBase' n i := by
    rw [IsEmbedding.image_imageCellMap, ← hD]
    exact (disjoint_image_iff hf.injective).2 (disjointBase n i)
  mapsTo n i := by
    obtain ⟨I, hI⟩ := RelCWComplex.mapsTo n i
    refine ⟨I, ?_⟩
    simp only [IsEmbedding.image_imageCellMap]
    rw [IsEmbedding.coe_imageCellMap, ← hD]
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
    · rw [hpre, ← IsEmbedding.image_imageCellMap hf.injective]
      exact (hA.1 n j).preimage hf.continuous
    · rw [hpre, hD]
      exact hA.2.preimage hf.continuous
  isClosedBase := hD ▸ hf.isClosedMap _ (isClosedBase C)
  union' := by
    have := congrArg (f '' ·) (RelCWComplex.union (C := C))
    simp only [image_union, image_iUnion, closedCell] at this
    simpa only [IsEmbedding.image_imageCellMap, hC, hD] using this

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
  IsEmbedding.image_imageCellMap hf.injective n _ _

/-- The closed cells of the image of `C` under `f` are the images of the closed cells of `C`. -/
@[simp]
lemma closedCell_relCWComplex (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) :
    @closedCell Y _ C' D' (hf.relCWComplex hC hD) n i =
      f '' closedCell n (hf.relCWComplexCellEquiv hC hD n i) :=
  IsEmbedding.image_imageCellMap hf.injective n _ _

/-- The boundaries of the cells of the image of `C` under `f` are the images of the boundaries of
the cells of `C`. -/
@[simp]
lemma cellFrontier_relCWComplex (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) :
    @cellFrontier Y _ C' D' (hf.relCWComplex hC hD) n i =
      f '' cellFrontier n (hf.relCWComplexCellEquiv hC hD n i) :=
  IsEmbedding.image_imageCellMap hf.injective n _ _

end Topology.IsClosedEmbedding

namespace Topology.IsOpenEmbedding

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
  (hf : IsOpenEmbedding f) {C D : Set X} [RelCWComplex C D] {C' D' : Set Y}

/-- **Extending a relative CW complex along an open embedding.** Let `f : X → Y` be an open
embedding, `C` a CW complex relative to `D` in `X`, and `D'` a closed subset of `Y` with
`f ⁻¹' D' = D` and `(range f)ᶜ ⊆ interior D'`. Then `C' = D' ∪ f '' C` is a CW complex relative to
`D'` in `Y`, with the cells of `C` and their characteristic maps followed by `f`. -/
@[instance_reducible]
def relCWComplex (hD' : IsClosed D') (hpre : f ⁻¹' D' = D) (hcompl : (range f)ᶜ ⊆ interior D')
    (hC' : D' ∪ f '' C = C') : RelCWComplex C' D' where
  cell := cell C
  map := IsEmbedding.imageCellMap hf.injective
  source_eq := IsEmbedding.source_imageCellMap hf.injective
  continuousOn n i := hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n i)
  continuousOn_symm := IsEmbedding.continuousOn_symm_imageCellMap hf.isEmbedding
  pairwiseDisjoint' := by
    rintro ⟨n, i⟩ - ⟨m, j⟩ - hne
    simp only [Function.onFun, IsEmbedding.image_imageCellMap]
    exact (disjoint_image_iff hf.injective).2 (pairwiseDisjoint (C := C) (mem_univ _)
      (mem_univ _) hne)
  disjointBase' n i := by
    rw [IsEmbedding.image_imageCellMap]
    refine disjoint_left.2 ?_
    rintro _ ⟨x, hx, rfl⟩ hxD'
    exact disjoint_left.1 (disjointBase (C := C) n i) hx (hpre ▸ hxD')
  mapsTo n i := by
    obtain ⟨I, hI⟩ := RelCWComplex.mapsTo n i
    refine ⟨I, ?_⟩
    simp only [IsEmbedding.image_imageCellMap]
    rw [IsEmbedding.coe_imageCellMap]
    refine ((mapsTo_image f _).comp hI).mono_right ?_
    rw [image_union]
    exact union_subset_union (image_subset_iff.2 hpre.symm.le)
      (by simp only [image_iUnion]; exact Subset.rfl)
  closed' A hAC hA := by
    -- Show `Aᶜ` is open using the open cover `{range f, interior D'}` of `Y`.
    rw [← isOpen_compl_iff]
    have hpreC : f ⁻¹' A ⊆ C := fun x hx ↦ by
      rcases hC' ▸ hAC hx with hxD' | ⟨x', hx', hxx'⟩
      · exact base_subset_complex (C := C) (hpre ▸ hxD')
      · exact hf.injective hxx' ▸ hx'
    have hpreClosed : IsClosed (f ⁻¹' A) := by
      refine RelCWComplex.closed' (C := C) (f ⁻¹' A) hpreC ⟨fun n j ↦ ?_, ?_⟩
      · have h : f ⁻¹' A ∩ map n j '' closedBall 0 1 =
            f ⁻¹' (A ∩ IsEmbedding.imageCellMap hf.injective n j '' closedBall 0 1) := by
          rw [IsEmbedding.image_imageCellMap, preimage_inter, preimage_image_eq _ hf.injective]
        rw [h]
        exact (hA.1 n j).preimage hf.continuous
      · rw [← hpre, ← preimage_inter]
        exact hA.2.preimage hf.continuous
    have hcomplEq : Aᶜ = f '' (f ⁻¹' A)ᶜ ∪ (interior D' ∩ (A ∩ D')ᶜ) := by
      ext y
      simp only [mem_compl_iff, mem_union, mem_image, mem_inter_iff]
      refine ⟨fun hy ↦ ?_, ?_⟩
      · by_cases hyr : y ∈ range f
        · obtain ⟨x, rfl⟩ := hyr
          exact .inl ⟨x, hy, rfl⟩
        · exact .inr ⟨hcompl hyr, fun h ↦ hy h.1⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨hyint, hyAD⟩)
        · exact hx
        · exact fun hyA ↦ hyAD ⟨hyA, interior_subset hyint⟩
    rw [hcomplEq]
    exact (hf.isOpenMap _ hpreClosed.isOpen_compl).union (isOpen_interior.inter hA.2.isOpen_compl)
  isClosedBase := hD'
  union' := by
    have hCD : f '' C = f '' D ∪ ⋃ n, ⋃ i : cell C n, f '' closedCell n i := by
      have := congrArg (f '' ·) (RelCWComplex.union (C := C)).symm
      simpa only [image_union, image_iUnion, closedCell] using this
    have hsub : D' ∪ f '' D = D' := union_eq_left.2 (image_subset_iff.2 hpre.symm.le)
    simp only [IsEmbedding.image_imageCellMap]
    calc
      (D' ∪ ⋃ n, ⋃ i : cell C n, f '' (map n i '' closedBall 0 1)) =
          (D' ∪ f '' D) ∪ ⋃ n, ⋃ i : cell C n, f '' closedCell n i := by
        rw [hsub]
        rfl
      _ = D' ∪ f '' C := by rw [union_assoc, ← hCD]
      _ = C' := hC'

variable (hD' : IsClosed D') (hpre : f ⁻¹' D' = D) (hcompl : (range f)ᶜ ⊆ interior D')
  (hC' : D' ∪ f '' C = C')

/-- The cells of `D' ∪ f '' C` relative to `D'` are the cells of `C`. -/
def relCWComplexCellEquiv (n : ℕ) :
    @cell Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') n ≃ cell C n :=
  Equiv.refl _

/-- The characteristic maps of `D' ∪ f '' C` relative to `D'` are those of `C` followed by `f`. -/
@[simp]
lemma coe_map_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') n) :
    ⇑(@map Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') n i) =
      f ∘ map n (hf.relCWComplexCellEquiv hD' hpre hcompl hC' n i) :=
  (rfl)

/-- The open cells of `D' ∪ f '' C` relative to `D'` are the images of the open cells of `C`. -/
@[simp]
lemma openCell_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') n) :
    @openCell Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') n i =
      f '' openCell n (hf.relCWComplexCellEquiv hD' hpre hcompl hC' n i) :=
  IsEmbedding.image_imageCellMap hf.injective n _ _

/-- The closed cells of `D' ∪ f '' C` relative to `D'` are the images of the closed cells of `C`. -/
@[simp]
lemma closedCell_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') n) :
    @closedCell Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') n i =
      f '' closedCell n (hf.relCWComplexCellEquiv hD' hpre hcompl hC' n i) :=
  IsEmbedding.image_imageCellMap hf.injective n _ _

/-- The cell frontiers of `D' ∪ f '' C` relative to `D'` are the images of the cell frontiers of
`C`. -/
@[simp]
lemma cellFrontier_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') n) :
    @cellFrontier Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') n i =
      f '' cellFrontier n (hf.relCWComplexCellEquiv hD' hpre hcompl hC' n i) :=
  IsEmbedding.image_imageCellMap hf.injective n _ _

/-- Finite-dimensionality transfers from `C` to `D' ∪ f '' C` relative to `D'`. -/
lemma finiteDimensional_relCWComplex [RelCWComplex.FiniteDimensional C] :
    @RelCWComplex.FiniteDimensional Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') :=
  @RelCWComplex.FiniteDimensional.mk Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') <| by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    exact (hf.relCWComplexCellEquiv hD' hpre hcompl hC' n).isEmpty_congr.2 hn

/-- Finite type transfers from `C` to `D' ∪ f '' C` relative to `D'`. -/
lemma finiteType_relCWComplex [RelCWComplex.FiniteType C] :
    @RelCWComplex.FiniteType Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') :=
  @RelCWComplex.FiniteType.mk Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') fun n ↦
    (hf.relCWComplexCellEquiv hD' hpre hcompl hC' n).finite_iff.2
      (FiniteType.finite_cell (C := C) (D := D) n)

/-- Finiteness transfers from `C` to `D' ∪ f '' C` relative to `D'`. -/
lemma finite_relCWComplex [RelCWComplex.Finite C] :
    @RelCWComplex.Finite Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC') :=
  @finite_of_finiteDimensional_finiteType Y _ C' D' (hf.relCWComplex hD' hpre hcompl hC')
    (hf.finiteDimensional_relCWComplex hD' hpre hcompl hC')
    (hf.finiteType_relCWComplex hD' hpre hcompl hC')

end Topology.IsOpenEmbedding
