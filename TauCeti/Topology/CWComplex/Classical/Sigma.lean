/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.Image

/-!
# Disjoint unions of CW complexes

An arbitrary disjoint union of relative CW complexes is a relative CW complex, with
one cell for each cell in each summand. Its characteristic maps are the original maps
followed by the summand inclusions. Closure-finiteness stays within a single summand,
and the weak topology follows from the coproduct topology. Neither local finiteness
nor a separation assumption is required.

The absolute construction is an instance. In particular, disjoint unions of spaces
with CW structures again carry CW structures. This allows componentwise constructions
of CW models to be assembled without a connectedness hypothesis.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 and the Appendix (CW complexes).

The characteristic maps reuse `IsClosedEmbedding.relCWComplex` for each summand.
-/

public noncomputable section

open Set Metric

namespace Topology.RelCWComplex

universe u

variable {ι : Type u} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  (C D : ∀ i, Set (X i)) [∀ i, RelCWComplex (C i) (D i)]

private def sigmaCellMap (n : ℕ) (i : ι) (j : cell (C i) n) :
    PartialEquiv (Fin n → ℝ) (Σ i, X i) :=
  @map _ _ _ _ (IsClosedEmbedding.sigmaMk.relCWComplex
    (C := C i) (D := D i) rfl rfl) n
    ((IsClosedEmbedding.sigmaMk.relCWComplexCellEquiv
      (C := C i) (D := D i) rfl rfl n).symm j)

private theorem sigmaCellMap_apply (n : ℕ) (i : ι) (j : cell (C i) n) (x : Fin n → ℝ) :
    sigmaCellMap C D n i j x = Sigma.mk i (map n j x) := by
  unfold sigmaCellMap
  rw [IsClosedEmbedding.coe_map_relCWComplex, Equiv.apply_symm_apply]
  rfl

private theorem sigmaCellMap_image (n : ℕ) (i : ι) (j : cell (C i) n)
    (T : Set (Fin n → ℝ)) :
    sigmaCellMap C D n i j '' T = Sigma.mk i '' (map n j '' T) := by
  simp only [← image_comp, Function.comp_def, sigmaCellMap_apply]

/-- The relative CW structure on a disjoint union. Cells retain their summand index.
This is not an instance, since the base of a relative CW structure is an output parameter. -/
@[instance_reducible]
def sigma : RelCWComplex (univ.sigma C) (univ.sigma D) :=
  let S (i : ι) := IsClosedEmbedding.sigmaMk.relCWComplex
    (C := C i) (D := D i) rfl rfl
  let e (i : ι) (n : ℕ) := IsClosedEmbedding.sigmaMk.relCWComplexCellEquiv
    (C := C i) (D := D i) rfl rfl n
  { cell n := Σ i, cell (C i) n
    map n c := sigmaCellMap C D n c.1 c.2
    source_eq n c := @source_eq _ _ _ _ (S c.1) n ((e c.1 n).symm c.2)
    continuousOn n c := @continuousOn _ _ _ _ (S c.1) n ((e c.1 n).symm c.2)
    continuousOn_symm n c := @continuousOn_symm _ _ _ _ (S c.1) n ((e c.1 n).symm c.2)
    pairwiseDisjoint' := by
      rintro ⟨n, i, c⟩ _ ⟨m, j, d⟩ _ hne
      simp only [Function.onFun, sigmaCellMap_image]
      by_cases hij : i = j
      · subst j
        apply (disjoint_image_iff sigma_mk_injective).2
        apply disjoint_openCell_of_ne
        intro h
        apply hne
        obtain ⟨rfl, rfl⟩ := Sigma.mk.inj_iff.mp h
        rfl
      · exact disjoint_left.2 fun z ⟨x, _, hx⟩ ⟨y, _, hy⟩ ↦
          hij ((Sigma.mk.inj_iff.mp (hx.trans hy.symm)).1)
    disjointBase' n c := by
      rw [sigmaCellMap_image]
      refine disjoint_left.2 ?_
      rintro z ⟨x, hx, rfl⟩ hz
      exact (disjointBase n c.2).notMem_of_mem_left hx hz.2
    mapsTo n c := by
      classical
      obtain ⟨J, hJ⟩ := cellFrontier_subset_base_union_finite_closedCell (C := C c.1) n c.2
      refine ⟨fun m ↦ (J m).map ⟨Sigma.mk c.1, sigma_mk_injective⟩, ?_⟩
      intro x hx
      rw [sigmaCellMap_apply]
      rcases hJ (mem_image_of_mem _ hx) with hD | h
      · exact Or.inl ⟨mem_univ _, hD⟩
      · simp only [mem_iUnion, exists_prop] at h
        obtain ⟨m, hmn, j, hj, hy⟩ := h
        simp only [mem_union, mem_iUnion, exists_prop, sigmaCellMap_image]
        exact Or.inr ⟨m, hmn, ⟨c.1, j⟩, Finset.mem_map.mpr ⟨j, hj, rfl⟩,
          mem_image_of_mem _ hy⟩
    closed' A hAC hA := by
      refine isClosed_sigma_iff.2 fun i ↦ ?_
      refine RelCWComplex.closed' (C := C i) (Sigma.mk i ⁻¹' A)
        (fun x hx ↦ (hAC hx).2) ⟨fun n j ↦ ?_, ?_⟩
      · have h := (hA.1 n ⟨i, j⟩).preimage (continuous_sigmaMk (i := i))
        simpa only [sigmaCellMap_image, preimage_inter,
          preimage_image_eq _ sigma_mk_injective] using h
      · simpa using hA.2.preimage (continuous_sigmaMk (i := i))
    isClosedBase := isClosed_sigma_iff.2 fun i ↦ by
      simpa using isClosedBase (C i)
    union' := by
      ext ⟨i, x⟩
      simp only [mem_union, mem_iUnion, sigmaCellMap_image]
      constructor
      · rintro (hx | ⟨n, ⟨j, c⟩, y, hy, hxy⟩)
        · exact ⟨mem_univ _, base_subset_complex hx.2⟩
        · obtain ⟨rfl, rfl⟩ := Sigma.mk.inj_iff.mp hxy
          exact ⟨mem_univ _, closedCell_subset_complex n c hy⟩
      · intro hx
        rcases (RelCWComplex.union (C := C i)).superset hx.2 with hxD | hx
        · exact Or.inl ⟨mem_univ _, hxD⟩
        · obtain ⟨n, j, hj⟩ := mem_iUnion₂.mp hx
          exact Or.inr ⟨n, ⟨i, j⟩, x, hj, rfl⟩ }

/-- The cells of a disjoint union are the cells of its summands, with their summand indices. -/
def sigmaCellEquiv (n : ℕ) :
    @cell _ _ (univ.sigma C) (univ.sigma D) (sigma C D) n ≃ Σ i, cell (C i) n :=
  Equiv.refl _

/-- A characteristic map in a disjoint union is followed by its summand inclusion. -/
@[simp]
theorem coe_map_sigma (n : ℕ) (i : ι) (j : cell (C i) n) :
    ⇑(@map _ _ _ _ (sigma C D) n ((sigmaCellEquiv C D n).symm ⟨i, j⟩)) =
      Sigma.mk i ∘ map n j := by
  funext x
  exact sigmaCellMap_apply C D n i j x

/-- Open cells in the disjoint union are images of open cells in the summands. -/
@[simp]
theorem openCell_sigma (n : ℕ) (i : ι) (j : cell (C i) n) :
    @openCell _ _ _ _ (sigma C D) n ((sigmaCellEquiv C D n).symm ⟨i, j⟩) =
      Sigma.mk i '' openCell n j :=
  sigmaCellMap_image C D n i j _

/-- Closed cells in the disjoint union are images of closed cells in the summands. -/
@[simp]
theorem closedCell_sigma (n : ℕ) (i : ι) (j : cell (C i) n) :
    @closedCell _ _ _ _ (sigma C D) n ((sigmaCellEquiv C D n).symm ⟨i, j⟩) =
      Sigma.mk i '' closedCell n j :=
  sigmaCellMap_image C D n i j _

/-- Cell frontiers in the disjoint union are images of frontiers in the summands. -/
@[simp]
theorem cellFrontier_sigma (n : ℕ) (i : ι) (j : cell (C i) n) :
    @cellFrontier _ _ _ _ (sigma C D) n ((sigmaCellEquiv C D n).symm ⟨i, j⟩) =
      Sigma.mk i '' cellFrontier n j :=
  sigmaCellMap_image C D n i j _

end Topology.RelCWComplex

namespace Topology.CWComplex

open RelCWComplex

universe u

variable {ι : Type u} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- An arbitrary disjoint union of CW complexes is a CW complex. -/
instance sigma (C : ∀ i, Set (X i)) [∀ i, CWComplex (C i)] :
    CWComplex (univ.sigma C) :=
  let S := RelCWComplex.sigma C (fun _ ↦ ∅)
  { cell := S.cell
    map := S.map
    source_eq := S.source_eq
    continuousOn := S.continuousOn
    continuousOn_symm := S.continuousOn_symm
    pairwiseDisjoint' := S.pairwiseDisjoint'
    mapsTo' n c := by simpa using S.mapsTo n c
    closed' A hAC hA := S.closed' A hAC ⟨hA, by simp⟩
    union' := by simpa using S.union' }

variable (C : ∀ i, Set (X i)) [∀ i, CWComplex (C i)]

/-- Cells in the absolute disjoint union retain their summand index. -/
def sigmaCellEquiv (n : ℕ) : cell (univ.sigma C) n ≃ Σ i, cell (C i) n :=
  Equiv.refl _

/-- Absolute characteristic maps are followed by the summand inclusion. -/
@[simp]
theorem coe_map_sigma (n : ℕ) (i : ι) (j : cell (C i) n) :
    ⇑(map n ((sigmaCellEquiv C n).symm ⟨i, j⟩)) = Sigma.mk i ∘ map n j :=
  RelCWComplex.coe_map_sigma C (fun _ ↦ ∅) n i j

/-- Absolute open cells are the summand images of the original open cells. -/
@[simp]
theorem openCell_sigma (n : ℕ) (i : ι) (j : cell (C i) n) :
    openCell n ((sigmaCellEquiv C n).symm ⟨i, j⟩) = Sigma.mk i '' openCell n j :=
  RelCWComplex.openCell_sigma C (fun _ ↦ ∅) n i j

/-- Absolute closed cells are the summand images of the original closed cells. -/
@[simp]
theorem closedCell_sigma (n : ℕ) (i : ι) (j : cell (C i) n) :
    closedCell n ((sigmaCellEquiv C n).symm ⟨i, j⟩) = Sigma.mk i '' closedCell n j :=
  RelCWComplex.closedCell_sigma C (fun _ ↦ ∅) n i j

/-- Absolute cell frontiers are the summand images of the original frontiers. -/
@[simp]
theorem cellFrontier_sigma (n : ℕ) (i : ι) (j : cell (C i) n) :
    cellFrontier n ((sigmaCellEquiv C n).symm ⟨i, j⟩) = Sigma.mk i '' cellFrontier n j :=
  RelCWComplex.cellFrontier_sigma C (fun _ ↦ ∅) n i j

omit C [∀ i, CWComplex (C i)] in
/-- A disjoint union of spaces with CW structures has a CW structure on the whole space. -/
instance sigmaUniv [∀ i, CWComplex (univ : Set (X i))] :
    CWComplex (univ : Set (Σ i, X i)) :=
  let S := sigma (fun i ↦ (univ : Set (X i)))
  { S with
    closed' A _ hA := S.closed' A (by simp) hA
    union' := by simpa using S.union' }

omit C [∀ i, CWComplex (C i)] in
section

variable [∀ i, CWComplex (univ : Set (X i))]

/-- Cells in the whole-space disjoint union retain their summand index. -/
def sigmaUnivCellEquiv (n : ℕ) :
    cell (univ : Set (Σ i, X i)) n ≃ Σ i, cell (univ : Set (X i)) n :=
  Equiv.refl _

/-- Whole-space characteristic maps are followed by the summand inclusion. -/
@[simp]
theorem coe_map_sigmaUniv (n : ℕ) (i : ι) (j : cell (univ : Set (X i)) n) :
    ⇑(map n ((sigmaUnivCellEquiv n).symm ⟨i, j⟩)) = Sigma.mk i ∘ map n j :=
  coe_map_sigma (fun i ↦ (univ : Set (X i))) n i j

/-- Whole-space open cells are the summand images of the original open cells. -/
@[simp]
theorem openCell_sigmaUniv (n : ℕ) (i : ι) (j : cell (univ : Set (X i)) n) :
    openCell n ((sigmaUnivCellEquiv n).symm ⟨i, j⟩) = Sigma.mk i '' openCell n j :=
  openCell_sigma (fun i ↦ (univ : Set (X i))) n i j

/-- Whole-space closed cells are the summand images of the original closed cells. -/
@[simp]
theorem closedCell_sigmaUniv (n : ℕ) (i : ι) (j : cell (univ : Set (X i)) n) :
    closedCell n ((sigmaUnivCellEquiv n).symm ⟨i, j⟩) = Sigma.mk i '' closedCell n j :=
  closedCell_sigma (fun i ↦ (univ : Set (X i))) n i j

/-- Whole-space cell frontiers are the summand images of the original frontiers. -/
@[simp]
theorem cellFrontier_sigmaUniv (n : ℕ) (i : ι) (j : cell (univ : Set (X i)) n) :
    cellFrontier n ((sigmaUnivCellEquiv n).symm ⟨i, j⟩) = Sigma.mk i '' cellFrontier n j :=
  cellFrontier_sigma (fun i ↦ (univ : Set (X i))) n i j

end

end Topology.CWComplex
