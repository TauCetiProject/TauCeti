/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
import TauCeti.Topology.Maps.DomRestrict

/-!
# Extending and pushing forward relative CW complexes along embeddings

Let `C` be a CW complex relative to `D` in `X`, and let `f : X → Y` be a map.

* Suppose that `f` restricts to an embedding on a closed set `S ⊇ C`. Let `D'` be a closed subset
  of `Y` with `f ⁻¹' D' ∩ C = D`, and suppose that the cells of `C` do not accumulate outside
  `f '' S`: `closure (f '' (C \ D)) ⊆ f '' S`. Then `C' = D' ∪ f '' C` is a CW complex relative
  to `D'` in `Y` (`Topology.IsEmbedding.relCWComplex`), with the same cells
  (`Topology.IsEmbedding.relCWComplexCellEquiv`), characteristic maps `f ∘ map n i`
  (`Topology.IsEmbedding.coe_map_relCWComplex`, `Topology.IsEmbedding.map_relCWComplex_symm_apply`),
  and finiteness properties (`Topology.IsEmbedding.finiteDimensional_relCWComplex`,
  `Topology.IsEmbedding.finiteType_relCWComplex`, and `Topology.IsEmbedding.finite_relCWComplex`).
  Away from `S` the map `f` is arbitrary. Without the closure condition, cells of `C` may
  accumulate at points outside `f '' S`, and then `D' ∪ f '' C` need not carry the weak topology
  in `Y`. For an embedding `f` and `S = univ`, the condition holds when `range f` is closed, and
  when `(range f)ᶜ ⊆ interior D'`, as for the open manifold part of a space whose complement lies
  in the interior of a sublevel set `D'`.
* When `f` is a closed embedding, `f '' C` is a CW complex relative to `f '' D` in `Y`
  (`Topology.IsClosedEmbedding.relCWComplex`, the case `S = univ` and `D' = f '' D` of the
  above), with the same cells (`Topology.IsClosedEmbedding.relCWComplexCellEquiv`), the
  characteristic maps of `C` followed by `f` (`Topology.IsClosedEmbedding.coe_map_relCWComplex`),
  and the same finiteness properties (`Topology.IsClosedEmbedding.finite_relCWComplex` and its
  siblings). For an absolute CW complex, the base is `f '' ∅ = ∅`, and
  `Topology.RelCWComplex.toCWComplex` turns the result into an absolute CW complex.

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

variable {X Y : Type u} [TopologicalSpace X] {f : X → Y} {S C D : Set X} [RelCWComplex C D]

/-- The characteristic map of a cell of `C`, followed by a map `f` that is injective on `S`. -/
private def imageCellMap (hinj : InjOn f S) (n : ℕ) (i : cell C n) :
    PartialEquiv (Fin n → ℝ) Y :=
  haveI : Nonempty X := ⟨map n i 0⟩
  (map n i).trans (hinj.toPartialEquiv f S)

private lemma coe_imageCellMap (hinj : InjOn f S) (n : ℕ) (i : cell C n) :
    ⇑(imageCellMap hinj n i) = f ∘ map n i :=
  rfl

private lemma image_imageCellMap (hinj : InjOn f S) (n : ℕ) (i : cell C n)
    (s : Set (Fin n → ℝ)) : imageCellMap hinj n i '' s = f '' (map n i '' s) := by
  rw [coe_imageCellMap, image_comp]

private lemma source_imageCellMap (hinj : InjOn f S) (hCS : C ⊆ S) (n : ℕ) (i : cell C n) :
    (imageCellMap hinj n i).source = ball 0 1 := by
  have : Nonempty X := ⟨map n i 0⟩
  rw [imageCellMap, PartialEquiv.trans_source, source_eq]
  exact inter_eq_left.2 fun x hx ↦ hCS (openCell_subset_complex n i ⟨x, hx, rfl⟩)

end Map

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {S : Set X}
  (hf : IsEmbedding (S.domRestrict f)) {C D : Set X} [RelCWComplex C D] {C' D' : Set Y}

private lemma continuousOn_symm_imageCellMap (n : ℕ) (i : cell C n) :
    ContinuousOn (imageCellMap (injOn_iff_injective.2 hf.injective) n i).symm
      (imageCellMap (injOn_iff_injective.2 hf.injective) n i).target := by
  have : Nonempty X := ⟨map n i 0⟩
  rw [imageCellMap, PartialEquiv.coe_trans_symm, PartialEquiv.trans_target]
  exact (continuousOn_symm n i).comp (hf.isInducing.continuousOn_invFunOn.mono inter_subset_left)
    fun y hy ↦ hy.2

/-- **The weak topology of `D' ∪ f '' C`.** Let `f` restrict to an embedding on a closed set
`S ⊇ C`, let `D ⊆ f ⁻¹' D'`, and suppose that `closure (f '' (C \ D)) ⊆ f '' S`. Then a set
`A ⊆ D' ∪ f '' C` is closed in `Y` if `A ∩ D'` and `A ∩ f '' closedCell n j`, for every cell `j`
of `C`, are closed in `Y`. -/
private lemma isClosed_of_isClosed_inter_imageCellMap (hS : IsClosed S) (hCS : C ⊆ S)
    (hDD' : D ⊆ f ⁻¹' D') (hcl : closure (f '' (C \ D)) ⊆ f '' S) {A : Set Y}
    (hAC : A ⊆ D' ∪ f '' C)
    (hA : (∀ n (j : cell C n), IsClosed
      (A ∩ imageCellMap (injOn_iff_injective.2 hf.injective) n j '' closedBall 0 1)) ∧
      IsClosed (A ∩ D')) :
    IsClosed A := by
  have hinj : InjOn f S := injOn_iff_injective.2 hf.injective
  have hfS : ContinuousOn f S := continuousOn_iff_continuous_domRestrict.2 hf.continuous
  -- First, `f ⁻¹' A ∩ C` is closed in `X` by the weak topology of `C`.
  have hpreClosed : IsClosed (f ⁻¹' A ∩ C) := by
    refine RelCWComplex.closed' (C := C) _ inter_subset_right ⟨fun n j ↦ ?_, ?_⟩
    · -- On a closed cell, it is the part of `S` that `f` maps to `A ∩ f '' closedCell n j`.
      have hsub : map n j '' closedBall 0 1 ⊆ C := closedCell_subset_complex n j
      have h : f ⁻¹' A ∩ C ∩ map n j '' closedBall 0 1 =
          f ⁻¹' (A ∩ imageCellMap hinj n j '' closedBall 0 1) ∩ S := by
        simp only [image_imageCellMap, preimage_inter, inter_assoc, inter_eq_right.2 hsub,
          hinj.preimage_image_inter (hsub.trans hCS)]
      rw [h, inter_comm]
      exact hfS.preimage_isClosed_of_isClosed hS (hA.1 n j)
    · -- On `D ⊆ C ∩ f ⁻¹' D'`, it is the preimage of `A ∩ D'`.
      have h : f ⁻¹' A ∩ C ∩ D = f ⁻¹' (A ∩ D') ∩ D := by
        simp only [preimage_inter, inter_assoc, inter_eq_right.2 (base_subset_complex (C := C)),
          inter_eq_right.2 hDD']
      rw [h, inter_comm]
      exact (hfS.mono ((base_subset_complex (C := C)).trans hCS)).preimage_isClosed_of_isClosed
        (isClosedBase C) hA.2
  -- Hence `f ⁻¹' A ∩ C` is cut out of `S` by a closed `F ⊆ Y`, so `F ∩ f '' S = A ∩ f '' C`.
  obtain ⟨F, hF, hFA⟩ := hf.isInducing.isClosed_iff.1 (hpreClosed.preimage continuous_subtypeVal)
  have hFA' (x : X) (hx : x ∈ S) : f x ∈ F ↔ f x ∈ A ∧ x ∈ C := Set.ext_iff.1 hFA ⟨x, hx⟩
  -- Off `D'`, `A` lies in `f '' (C \ D)`, whose closure lies in `f '' S`.
  have hAeq : A = (F ∩ closure (f '' (C \ D))) ∪ (A ∩ D') := by
    refine subset_antisymm (fun y hy ↦ ?_) (union_subset ?_ inter_subset_left)
    · by_cases hyD' : y ∈ D'
      · exact .inr ⟨hy, hyD'⟩
      obtain ⟨x, hx, rfl⟩ := (hAC hy).resolve_left hyD'
      exact .inl ⟨(hFA' x (hCS hx)).2 ⟨hy, hx⟩,
        subset_closure ⟨x, ⟨hx, fun hxD ↦ hyD' (hDD' hxD)⟩, rfl⟩⟩
    · rintro y ⟨hyF, hy⟩
      obtain ⟨x, hx, rfl⟩ := hcl hy
      exact ((hFA' x hx).1 hyF).1
  rw [hAeq]
  exact (hF.inter isClosed_closure).union hA.2

/-- **Extending a relative CW complex along an embedding.** Let `C` be a CW complex relative to `D`
in `X`, and let `f : X → Y` restrict to an embedding on a closed set `S ⊇ C`. Let `D'` be a closed
subset of `Y` with `f ⁻¹' D' ∩ C = D` such that the cells of `C` do not accumulate outside `f '' S`:
`closure (f '' (C \ D)) ⊆ f '' S`. Then `C' = D' ∪ f '' C` is a CW complex relative to `D'` in
`Y`, with the cells of `C` and their characteristic maps followed by `f`. -/
@[instance_reducible]
def relCWComplex (hS : IsClosed S) (hCS : C ⊆ S) (hD' : IsClosed D') (hpre : f ⁻¹' D' ∩ C = D)
    (hcl : closure (f '' (C \ D)) ⊆ f '' S) (hC' : D' ∪ f '' C = C') : RelCWComplex C' D' where
  cell := cell C
  map := imageCellMap (injOn_iff_injective.2 hf.injective)
  source_eq := source_imageCellMap (injOn_iff_injective.2 hf.injective) hCS
  continuousOn n i := (continuousOn_iff_continuous_domRestrict.2 hf.continuous).comp
    (RelCWComplex.continuousOn n i)
    ((mapsTo_image _ _).mono_right ((closedCell_subset_complex n i).trans hCS))
  continuousOn_symm := continuousOn_symm_imageCellMap hf
  pairwiseDisjoint' := by
    rintro ⟨n, i⟩ - ⟨m, j⟩ - hne
    simp only [Function.onFun, image_imageCellMap]
    exact (pairwiseDisjoint (C := C) (mem_univ _) (mem_univ _) hne).image
      (injOn_iff_injective.2 hf.injective) ((openCell_subset_complex n i).trans hCS)
      ((openCell_subset_complex m j).trans hCS)
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
  closed' _ hAC hA := isClosed_of_isClosed_inter_imageCellMap hf hS hCS
    (hpre ▸ inter_subset_left) hcl (hC' ▸ hAC) hA
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

variable (hS : IsClosed S) (hCS : C ⊆ S) (hD' : IsClosed D') (hpre : f ⁻¹' D' ∩ C = D)
  (hcl : closure (f '' (C \ D)) ⊆ f '' S) (hC' : D' ∪ f '' C = C')

/-- The cells of `D' ∪ f '' C` relative to `D'` are the cells of `C`. -/
def relCWComplexCellEquiv (n : ℕ) :
    @cell Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n ≃ cell C n :=
  Equiv.refl _

/-- The characteristic maps of `D' ∪ f '' C` relative to `D'` are those of `C` followed by `f`. -/
@[simp]
lemma coe_map_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n) :
    ⇑(@map Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n i) =
      f ∘ map n (hf.relCWComplexCellEquiv hS hCS hD' hpre hcl hC' n i) :=
  (rfl)

/-- At `f x`, for `x ∈ S`, the inverse of a characteristic map of `D' ∪ f '' C` relative to `D'`
takes the value at `x` of the inverse of the corresponding characteristic map of `C`. For `x` in
the open cell, these are the coordinates of `x` in that cell. -/
@[simp]
lemma map_relCWComplex_symm_apply (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n) {x : X} (hx : x ∈ S) :
    (@map Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n i).symm (f x) =
      (map n (hf.relCWComplexCellEquiv hS hCS hD' hpre hcl hC' n i)).symm x :=
  have : Nonempty X := ⟨x⟩
  congrArg (map n _).symm ((injOn_iff_injective.2 hf.injective).leftInvOn_invFunOn hx)

/-- The open cells of `D' ∪ f '' C` relative to `D'` are the images of the open cells of `C`. -/
@[simp]
lemma openCell_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n) :
    @openCell Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n i =
      f '' openCell n (hf.relCWComplexCellEquiv hS hCS hD' hpre hcl hC' n i) :=
  image_imageCellMap _ n _ _

/-- The closed cells of `D' ∪ f '' C` relative to `D'` are the images of the closed cells of `C`. -/
@[simp]
lemma closedCell_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n) :
    @closedCell Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n i =
      f '' closedCell n (hf.relCWComplexCellEquiv hS hCS hD' hpre hcl hC' n i) :=
  image_imageCellMap _ n _ _

/-- The cell frontiers of `D' ∪ f '' C` relative to `D'` are the images of the cell frontiers of
`C`. -/
@[simp]
lemma cellFrontier_relCWComplex (n : ℕ)
    (i : @cell Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n) :
    @cellFrontier Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') n i =
      f '' cellFrontier n (hf.relCWComplexCellEquiv hS hCS hD' hpre hcl hC' n i) :=
  image_imageCellMap _ n _ _

/-- Finite-dimensionality transfers from `C` to `D' ∪ f '' C` relative to `D'`. -/
lemma finiteDimensional_relCWComplex [RelCWComplex.FiniteDimensional C] :
    @RelCWComplex.FiniteDimensional Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') :=
  @RelCWComplex.FiniteDimensional.mk Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC')
    (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))

/-- Finite type transfers from `C` to `D' ∪ f '' C` relative to `D'`. -/
lemma finiteType_relCWComplex [RelCWComplex.FiniteType C] :
    @RelCWComplex.FiniteType Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') :=
  @RelCWComplex.FiniteType.mk Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC')
    (FiniteType.finite_cell (C := C) (D := D))

/-- Finiteness transfers from `C` to `D' ∪ f '' C` relative to `D'`. -/
lemma finite_relCWComplex [RelCWComplex.Finite C] :
    @RelCWComplex.Finite Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC') :=
  @finite_of_finiteDimensional_finiteType Y _ C' D' (hf.relCWComplex hS hCS hD' hpre hcl hC')
    (hf.finiteDimensional_relCWComplex hS hCS hD' hpre hcl hC')
    (hf.finiteType_relCWComplex hS hCS hD' hpre hcl hC')

end Topology.IsEmbedding

namespace Topology.IsClosedEmbedding

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
  (hf : IsClosedEmbedding f) {C D : Set X} [RelCWComplex C D] {C' D' : Set Y}

/-- **The image of a relative CW complex under a closed embedding.** If `f` is a closed embedding
and `C` is a CW complex relative to `D`, then `C' = f '' C` is a CW complex relative to
`D' = f '' D`, with the cells of `C` and their characteristic maps followed by `f`. This is
`Topology.IsEmbedding.relCWComplex` for `S = univ`, whose closure condition holds since `range f`
is closed. -/
@[instance_reducible]
def relCWComplex (hC : f '' C = C') (hD : f '' D = D') : RelCWComplex C' D' :=
  IsEmbedding.relCWComplex (S := univ) (hf.isEmbedding.comp .subtypeVal) isClosed_univ
    (subset_univ C) (hD ▸ hf.isClosedMap _ (isClosedBase C))
    (by rw [← hD, hf.injective.preimage_image, inter_eq_left.2 base_subset_complex])
    (image_univ (f := f) ▸ hf.isClosed_range.closure_subset_iff.2 (image_subset_range _ _))
    (hC ▸ hD ▸ union_eq_right.2 (image_mono base_subset_complex))

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
  IsEmbedding.image_imageCellMap hf.injective.injOn n _ _

/-- The closed cells of the image of `C` under `f` are the images of the closed cells of `C`. -/
@[simp]
lemma closedCell_relCWComplex (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) :
    @closedCell Y _ C' D' (hf.relCWComplex hC hD) n i =
      f '' closedCell n (hf.relCWComplexCellEquiv hC hD n i) :=
  IsEmbedding.image_imageCellMap hf.injective.injOn n _ _

/-- The boundaries of the cells of the image of `C` under `f` are the images of the boundaries of
the cells of `C`. -/
@[simp]
lemma cellFrontier_relCWComplex (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) :
    @cellFrontier Y _ C' D' (hf.relCWComplex hC hD) n i =
      f '' cellFrontier n (hf.relCWComplexCellEquiv hC hD n i) :=
  IsEmbedding.image_imageCellMap hf.injective.injOn n _ _

/-- At `f x`, the inverse of a characteristic map of the image of `C` under a closed embedding `f`
takes the value at `x` of the inverse of the corresponding characteristic map of `C`. For `x` in
the open cell, these are the coordinates of `x` in that cell. -/
@[simp]
lemma map_relCWComplex_symm_apply (n : ℕ) (i : @cell Y _ C' D' (hf.relCWComplex hC hD) n) (x : X) :
    (@map Y _ C' D' (hf.relCWComplex hC hD) n i).symm (f x) =
      (map n (hf.relCWComplexCellEquiv hC hD n i)).symm x :=
  IsEmbedding.map_relCWComplex_symm_apply _ _ _ _ _ _ _ n i (mem_univ x)

/-- Finite-dimensionality transfers from `C` to its image under a closed embedding. -/
lemma finiteDimensional_relCWComplex [RelCWComplex.FiniteDimensional C] :
    @RelCWComplex.FiniteDimensional Y _ C' D' (hf.relCWComplex hC hD) :=
  IsEmbedding.finiteDimensional_relCWComplex _ _ _ _ _ _ _

/-- Finite type transfers from `C` to its image under a closed embedding. -/
lemma finiteType_relCWComplex [RelCWComplex.FiniteType C] :
    @RelCWComplex.FiniteType Y _ C' D' (hf.relCWComplex hC hD) :=
  IsEmbedding.finiteType_relCWComplex _ _ _ _ _ _ _

/-- Finiteness transfers from `C` to its image under a closed embedding. -/
lemma finite_relCWComplex [RelCWComplex.Finite C] :
    @RelCWComplex.Finite Y _ C' D' (hf.relCWComplex hC hD) :=
  IsEmbedding.finite_relCWComplex _ _ _ _ _ _ _

end Topology.IsClosedEmbedding
