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

* Let `D'` be a closed subset of `Y` with `f ⁻¹' D' ∩ C = D`, and suppose that the cells of `C`
  do not accumulate outside the range of `f`: `closure (f '' (C \ D)) ⊆ range f`. Then
  `C' = D' ∪ f '' C` is a CW complex relative to `D'` in `Y` (`Topology.IsEmbedding.relCWComplex`),
  with the same cells (`Topology.IsEmbedding.relCWComplexCellEquiv`), characteristic maps
  `f ∘ map n i` (`Topology.IsEmbedding.coe_map_relCWComplex`), and finiteness properties
  (`Topology.IsEmbedding.finiteDimensional_relCWComplex`,
  `Topology.IsEmbedding.finiteType_relCWComplex`, and `Topology.IsEmbedding.finite_relCWComplex`).
  Without the closure condition, cells of `C` may accumulate at points outside `range f`, and
  then `D' ∪ f '' C` need not carry the weak topology in `Y`. The condition holds when `range f`
  is closed, and when `(range f)ᶜ ⊆ interior D'`, as for the open manifold part of a space whose
  complement lies in the interior of a sublevel set `D'`.
* When `f` is a closed embedding, `f '' C` is a CW complex relative to `f '' D` in `Y`
  (`Topology.IsClosedEmbedding.relCWComplex`, the case `D' = f '' D` of the above), with the
  same cells (`Topology.IsClosedEmbedding.relCWComplexCellEquiv`) and the characteristic maps of
  `C` followed by `f` (`Topology.IsClosedEmbedding.coe_map_relCWComplex`). For an absolute CW
  complex, the base is `f '' ∅ = ∅`, and `Topology.RelCWComplex.toCWComplex` turns the result into
  an absolute CW complex.

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

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
  (hf : IsEmbedding f) {C D : Set X} [RelCWComplex C D] {C' D' : Set Y}

private lemma continuousOn_symm_imageCellMap (n : ℕ) (i : cell C n) :
    ContinuousOn (imageCellMap hf.injective n i).symm (imageCellMap hf.injective n i).target := by
  have : Nonempty X := ⟨map n i 0⟩
  have hinv : ContinuousOn (invFunOn f univ) (f '' univ) := by
    refine hf.isInducing.continuousOn_iff.2 (continuousOn_id.congr fun y hy ↦ ?_)
    obtain ⟨x, hx, rfl⟩ := hy
    exact invFunOn_eq ⟨x, hx, rfl⟩
  rw [imageCellMap, PartialEquiv.coe_trans_symm, PartialEquiv.trans_target]
  exact (continuousOn_symm n i).comp (hinv.mono inter_subset_left) fun y hy ↦ hy.2

/-- The weak topology of `C' = D' ∪ f '' C`: a subset `A ⊆ C'` whose intersections with `D'` and
with every closed cell `f '' closedCell n j` are closed is closed. -/
private lemma isClosed_of_isClosed_inter_imageCellMap (hpre : f ⁻¹' D' ∩ C = D)
    (hcl : closure (f '' (C \ D)) ⊆ range f) (hC' : D' ∪ f '' C = C') {A : Set Y} (hAC : A ⊆ C')
    (hA : (∀ n (j : cell C n), IsClosed (A ∩ imageCellMap hf.injective n j '' closedBall 0 1)) ∧
      IsClosed (A ∩ D')) :
    IsClosed A := by
  -- First, `f ⁻¹' A ∩ C` is closed in `X` by the weak topology of `C`.
  have hpreClosed : IsClosed (f ⁻¹' A ∩ C) := by
    refine RelCWComplex.closed' (C := C) _ inter_subset_right ⟨fun n j ↦ ?_, ?_⟩
    · -- The closed cells of `C` lie in `C`.
      have hsub : map n j '' closedBall 0 1 ⊆ C := closedCell_subset_complex n j
      have h : f ⁻¹' A ∩ C ∩ map n j '' closedBall 0 1 =
          f ⁻¹' (A ∩ imageCellMap hf.injective n j '' closedBall 0 1) := by
        rw [inter_assoc, inter_eq_right.2 hsub, image_imageCellMap, preimage_inter,
          preimage_image_eq _ hf.injective]
      rw [h]
      exact (hA.1 n j).preimage hf.continuous
    · -- Since `D ⊆ C ∩ f ⁻¹' D'`, this is the preimage of `A ∩ D'`, intersected with `D`.
      have h : f ⁻¹' A ∩ C ∩ D = f ⁻¹' (A ∩ D') ∩ D := by
        ext x
        refine ⟨fun ⟨⟨hxA, _⟩, hxD⟩ ↦ ⟨⟨hxA, ?_⟩, hxD⟩,
          fun ⟨⟨hxA, _⟩, hxD⟩ ↦ ⟨⟨hxA, base_subset_complex hxD⟩, hxD⟩⟩
        exact (hpre ▸ hxD : x ∈ f ⁻¹' D' ∩ C).1
      rw [h]
      exact (hA.2.preimage hf.continuous).inter (isClosedBase C)
  -- Hence `f ⁻¹' A ∩ C = f ⁻¹' F` for a closed `F ⊆ Y`. Off `D'`, `A` lies in
  -- `f '' (C \ D)`, whose closure lies in `range f`, where `A` and `F` agree.
  obtain ⟨F, hF, hFA⟩ := hf.isInducing.isClosed_iff.1 hpreClosed
  have hAeq : A = (F ∩ closure (f '' (C \ D))) ∪ (A ∩ D') := by
    refine subset_antisymm (fun y hy ↦ ?_) (union_subset ?_ inter_subset_left)
    · by_cases hyD' : y ∈ D'
      · exact .inr ⟨hy, hyD'⟩
      obtain ⟨x, hx, rfl⟩ := (hC' ▸ hAC hy).resolve_left hyD'
      have hxF : x ∈ f ⁻¹' F := hFA ▸ ⟨hy, hx⟩
      refine .inl ⟨hxF, subset_closure ⟨x, ⟨hx, fun hxD ↦ hyD' ?_⟩, rfl⟩⟩
      exact (hpre ▸ hxD : x ∈ f ⁻¹' D' ∩ C).1
    · rintro y ⟨hyF, hy⟩
      obtain ⟨x, rfl⟩ := hcl hy
      exact (hFA ▸ hyF : x ∈ f ⁻¹' A ∩ C).1
  rw [hAeq]
  exact (hF.inter isClosed_closure).union hA.2

/-- **Extending a relative CW complex along an embedding.** Let `f : X → Y` be an embedding, `C` a
CW complex relative to `D` in `X`, and `D'` a closed subset of `Y` with `f ⁻¹' D' ∩ C = D` such that
the cells of `C` do not accumulate outside the range of `f`:
`closure (f '' (C \ D)) ⊆ range f`. Then `C' = D' ∪ f '' C` is a CW complex relative to `D'` in
`Y`, with the cells of `C` and their characteristic maps followed by `f`. -/
@[instance_reducible]
def relCWComplex (hD' : IsClosed D') (hpre : f ⁻¹' D' ∩ C = D)
    (hcl : closure (f '' (C \ D)) ⊆ range f) (hC' : D' ∪ f '' C = C') : RelCWComplex C' D' where
  cell := cell C
  map := imageCellMap hf.injective
  source_eq := source_imageCellMap hf.injective
  continuousOn n i := hf.continuous.comp_continuousOn (RelCWComplex.continuousOn n i)
  continuousOn_symm := continuousOn_symm_imageCellMap hf
  pairwiseDisjoint' := by
    rintro ⟨n, i⟩ - ⟨m, j⟩ - hne
    simp only [Function.onFun, image_imageCellMap]
    exact (disjoint_image_iff hf.injective).2 (pairwiseDisjoint (C := C) (mem_univ _)
      (mem_univ _) hne)
  disjointBase' n i := by
    rw [image_imageCellMap, disjoint_image_left]
    exact disjoint_left.2 fun x hx hxD' ↦ disjoint_left.1 (disjointBase (C := C) n i) hx
      (hpre ▸ ⟨hxD', openCell_subset_complex n i hx⟩)
  mapsTo n i := by
    obtain ⟨I, hI⟩ := RelCWComplex.mapsTo n i
    refine ⟨I, ?_⟩
    simp only [image_imageCellMap]
    rw [coe_imageCellMap]
    refine ((mapsTo_image f _).comp hI).mono_right ?_
    rw [image_union]
    exact union_subset_union (image_subset_iff.2 (hpre ▸ inter_subset_left))
      (by simp only [image_iUnion]; exact Subset.rfl)
  closed' _ hAC hA := isClosed_of_isClosed_inter_imageCellMap hf hpre hcl hC' hAC hA
  isClosedBase := hD'
  union' := by
    have hCD : f '' C = f '' D ∪ ⋃ n, ⋃ i : cell C n, f '' closedCell n i := by
      have := congrArg (f '' ·) (RelCWComplex.union (C := C)).symm
      simpa only [image_union, image_iUnion, closedCell] using this
    have hsub : D' ∪ f '' D = D' :=
      union_eq_left.2 (image_subset_iff.2 (hpre ▸ inter_subset_left))
    simp only [image_imageCellMap]
    calc
      (D' ∪ ⋃ n, ⋃ i : cell C n, f '' (map n i '' closedBall 0 1)) =
          (D' ∪ f '' D) ∪ ⋃ n, ⋃ i : cell C n, f '' closedCell n i := by
        rw [hsub]
        simp only [closedCell]
      _ = D' ∪ f '' C := by rw [union_assoc, ← hCD]
      _ = C' := hC'

variable (hD' : IsClosed D') (hpre : f ⁻¹' D' ∩ C = D) (hcl : closure (f '' (C \ D)) ⊆ range f)
  (hC' : D' ∪ f '' C = C')

/-- The cells of `D' ∪ f '' C` relative to `D'` are the cells of `C`. -/
def relCWComplexCellEquiv (n : ℕ) :
    @cell Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') n ≃ cell C n :=
  Equiv.refl _

/-- The characteristic maps of `D' ∪ f '' C` relative to `D'` are those of `C` followed by `f`. -/
@[simp]
lemma coe_map_relCWComplex (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') n) :
    ⇑(@map Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') n i) =
      f ∘ map n (hf.relCWComplexCellEquiv hD' hpre hcl hC' n i) :=
  (rfl)

/-- The open cells of `D' ∪ f '' C` relative to `D'` are the images of the open cells of `C`. -/
@[simp]
lemma openCell_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') n) :
    @openCell Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') n i =
      f '' openCell n (hf.relCWComplexCellEquiv hD' hpre hcl hC' n i) :=
  image_imageCellMap hf.injective n _ _

/-- The closed cells of `D' ∪ f '' C` relative to `D'` are the images of the closed cells of `C`. -/
@[simp]
lemma closedCell_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') n) :
    @closedCell Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') n i =
      f '' closedCell n (hf.relCWComplexCellEquiv hD' hpre hcl hC' n i) :=
  image_imageCellMap hf.injective n _ _

/-- The cell frontiers of `D' ∪ f '' C` relative to `D'` are the images of the cell frontiers of
`C`. -/
@[simp]
lemma cellFrontier_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') n) :
    @cellFrontier Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') n i =
      f '' cellFrontier n (hf.relCWComplexCellEquiv hD' hpre hcl hC' n i) :=
  image_imageCellMap hf.injective n _ _

/-- Finite-dimensionality transfers from `C` to `D' ∪ f '' C` relative to `D'`. -/
lemma finiteDimensional_relCWComplex [RelCWComplex.FiniteDimensional C] :
    @RelCWComplex.FiniteDimensional Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') :=
  @RelCWComplex.FiniteDimensional.mk Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') <| by
    filter_upwards [FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D)] with n hn
    exact (hf.relCWComplexCellEquiv hD' hpre hcl hC' n).isEmpty_congr.2 hn

/-- Finite type transfers from `C` to `D' ∪ f '' C` relative to `D'`. -/
lemma finiteType_relCWComplex [RelCWComplex.FiniteType C] :
    @RelCWComplex.FiniteType Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') :=
  @RelCWComplex.FiniteType.mk Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') fun n ↦
    (hf.relCWComplexCellEquiv hD' hpre hcl hC' n).finite_iff.2
      (FiniteType.finite_cell (C := C) (D := D) n)

/-- Finiteness transfers from `C` to `D' ∪ f '' C` relative to `D'`. -/
lemma finite_relCWComplex [RelCWComplex.Finite C] :
    @RelCWComplex.Finite Y _ C' D' (hf.relCWComplex hD' hpre hcl hC') :=
  @finite_of_finiteDimensional_finiteType Y _ C' D' (hf.relCWComplex hD' hpre hcl hC')
    (hf.finiteDimensional_relCWComplex hD' hpre hcl hC')
    (hf.finiteType_relCWComplex hD' hpre hcl hC')

end Topology.IsEmbedding

namespace Topology.IsClosedEmbedding

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
  (hf : IsClosedEmbedding f) {C D : Set X} [RelCWComplex C D] {C' D' : Set Y}

/-- **The image of a relative CW complex under a closed embedding.** If `f` is a closed embedding
and `C` is a CW complex relative to `D`, then `C' = f '' C` is a CW complex relative to
`D' = f '' D`, with the cells of `C` and their characteristic maps followed by `f`. This is
`Topology.IsEmbedding.relCWComplex`, whose closure condition holds since `range f` is closed. -/
@[instance_reducible]
def relCWComplex (hC : f '' C = C') (hD : f '' D = D') : RelCWComplex C' D' :=
  -- The structure eta-expansion `{ _ with }` keeps the simp lemmas of
  -- `Topology.IsEmbedding.relCWComplex` from rewriting the cells of this structure, so that the
  -- simp lemmas below are its normal forms.
  { hf.isEmbedding.relCWComplex (hD ▸ hf.isClosedMap _ (isClosedBase C))
      (by rw [← hD, preimage_image_eq _ hf.injective,
        inter_eq_left.2 (base_subset_complex (C := C))])
      (hf.isClosed_range.closure_subset_iff.2 (image_subset_range _ _))
      (by rw [← hC, ← hD, union_eq_right.2 (image_mono (base_subset_complex (C := C)))]) with }

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
