/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.DiscBundle.Basic
import TauCeti.Topology.FiberBundle.Separation
import TauCeti.Topology.Separation.InvFunOn

/-!
# CW structures on the disc bundle subtype

This file transports the classical relative CW structures `TauCeti.relCWComplexDiscBundleRel` and
`TauCeti.relCWComplexDiscBundleSphereBundle` from the ambient total space `TotalSpace F E` to the
subtype `TauCeti.discBundle F E` (`D(E)`).

## Main definitions

* `TauCeti.relCWComplexDiscBundleSubtypeRel`: for a relative CW pair `(B, A)`, `D(E)` is a
  classical CW complex on `univ` relative to `S(E) ∪ D(E)|_A`.
* `TauCeti.relCWComplexDiscBundleSubtypeSphereBundle`: for a CW complex `B`, `D(E)` is a
  classical CW complex on `univ` relative to `S(E)`.
* `TauCeti.relCWComplexDiscBundleSubtypeRelCellEquiv`,
  `TauCeti.relCWComplexDiscBundleSubtypeSphereBundleCellEquiv`: the corresponding cell equivalences.

## Main results

* `TauCeti.closedCell_relCWComplexDiscBundleSubtypeRel`,
  `TauCeti.openCell_relCWComplexDiscBundleSubtypeRel`,
  `TauCeti.cellFrontier_relCWComplexDiscBundleSubtypeRel`, and their sphere-bundle analogues:
  explicit formulas for closed cells, open cells, and cell boundaries in `D(E)`.
* `TauCeti.finite_relCWComplexDiscBundleSubtypeRel` and
  `TauCeti.finite_relCWComplexDiscBundleSubtypeSphereBundle`: finiteness preservation in `D(E)`.
-/

public section

noncomputable section

open Bundle Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

section Sets

variable {B : Type u} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type u) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [FiberBundle F E]

private lemma discSubtypeBase_eq_preimage (A : Set B) :
    (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A : Set (discBundle F E)) =
      Subtype.val ⁻¹' (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A) := by
  ext v
  simp [discBundleProj_apply]

private theorem subtype_sphereBundle_union_empty :
    (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' (∅ : Set B) :
        Set (discBundle F E)) = Subtype.val ⁻¹' sphereBundle F E := by
  simp

end Sets

section Helpers

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] (A : Set B) [RelCWComplex (univ : Set B) A]

/-- Retracted characteristic map for a cell of `D(E)` taking values in the subtype
`discBundle F E`. -/
private def discSubtypeFun {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) (x : Fin n → ℝ) :
    discBundle F E :=
  letI := relCWComplexDiscBundleRel F E A
  ⟨map n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) (radialRetraction 1 x),
    closedCell_subset_complex n _
      (mem_image_of_mem _ (radialRetraction_mem_closedBall zero_le_one x))⟩

private theorem coe_discSubtypeFun_of_mem {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := relCWComplexDiscBundleRel F E A
    (discSubtypeFun F E A c x : TotalSpace F E) =
      map n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) x := by
  dsimp only [discSubtypeFun]
  rw [radialRetraction_of_norm_le (mem_closedBall_zero_iff.1 hx)]

private theorem continuous_discSubtypeFun {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    Continuous (discSubtypeFun F E A c) := by
  let _ := relCWComplexDiscBundleRel F E A
  refine Continuous.subtype_mk ?_ _
  exact (RelCWComplex.continuousOn n _).comp_continuous
    (lipschitzWith_radialRetraction zero_le_one).continuous
    (radialRetraction_mem_closedBall zero_le_one)

private theorem image_discSubtypeFun {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)
    {S : Set (Fin n → ℝ)} (hS : S ⊆ closedBall 0 1) :
    letI := relCWComplexDiscBundleRel F E A
    discSubtypeFun F E A c '' S =
      Subtype.val ⁻¹' (map n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) '' S) := by
  let _ := relCWComplexDiscBundleRel F E A
  ext v
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (coe_discSubtypeFun_of_mem F E A c (hS hx)).symm⟩
  · rintro ⟨x, hx, hxv⟩
    exact ⟨x, hx, Subtype.ext ((coe_discSubtypeFun_of_mem F E A c (hS hx)).trans hxv)⟩

private theorem injOn_discSubtypeFun {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    InjOn (discSubtypeFun F E A c) (ball 0 1) := by
  let _ := relCWComplexDiscBundleRel F E A
  intro x hx x' hx' h
  have hval := congrArg Subtype.val h
  rw [coe_discSubtypeFun_of_mem F E A c (ball_subset_closedBall hx),
    coe_discSubtypeFun_of_mem F E A c (ball_subset_closedBall hx')] at hval
  exact (map n _).injOn (by rw [source_eq]; exact hx) (by rw [source_eq]; exact hx') hval

private def discSubtypeMap {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    PartialEquiv (Fin n → ℝ) (discBundle F E) :=
  (injOn_discSubtypeFun F E A c).toPartialEquiv _ _

private theorem coe_discSubtypeMap {n : ℕ}
    (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m) :
    ⇑(discSubtypeMap F E A c) = discSubtypeFun F E A c := by
  rw [discSubtypeMap, InjOn.toPartialEquiv, BijOn.toPartialEquiv_apply]

end Helpers

section DiscBundleSubtype

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] (A : Set B) [RelCWComplex (univ : Set B) A]

open Classical in
/-- **The disc bundle subtype over a relative CW pair `(B, A)`.** If `(univ : Set B)` is a
classical CW complex relative to `A`, then `discBundle F E` is a classical CW complex on `univ`
relative to `S(E) ∪ D(E)|_A`, with one `(m + r)`-cell for each relative `m`-cell of `(B, A)`
(`TauCeti.relCWComplexDiscBundleSubtypeRelCellEquiv`). -/
@[instance_reducible]
def relCWComplexDiscBundleSubtypeRel :
    RelCWComplex (univ : Set (discBundle F E))
      (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A) :=
  letI := relCWComplexDiscBundleRel F E A
  { cell := fun n ↦ Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m
    map := fun _ c ↦ discSubtypeMap F E A c
    source_eq := fun _ _ ↦ rfl
    continuousOn := fun _ c ↦ by
      rw [coe_discSubtypeMap]
      exact (continuous_discSubtypeFun F E A c).continuousOn
    continuousOn_symm := fun n c ↦ by
      refine ContinuousOn.continuousOn_invFunOn_image_of_isCompact
        (continuous_discSubtypeFun F E A c).continuousOn
        (isCompact_closedBall 0 1) ball_subset_closedBall (injOn_discSubtypeFun F E A c) ?_
      rw [closedBall_sdiff_ball, image_discSubtypeFun F E A c sphere_subset_closedBall,
        image_discSubtypeFun F E A c ball_subset_closedBall]
      exact ((disjoint_skeletonLT_openCell le_rfl).mono_left
        (cellFrontier_subset_skeletonLT n _)).preimage _
    pairwiseDisjoint' := by
      rintro ⟨n, c⟩ - ⟨n', c'⟩ - hne
      simp only [Function.onFun, coe_discSubtypeMap,
        image_discSubtypeFun F E A _ ball_subset_closedBall]
      -- Transport cell inequality from the subtype structure back to `relCWComplexDiscBundleRel`.
      have hne' :
          (⟨n, (relCWComplexDiscBundleRelCellEquiv F E A n).symm c⟩ :
              Σ k, cell (discBundle F E) k) ≠
            ⟨n', (relCWComplexDiscBundleRelCellEquiv F E A n').symm c'⟩ := by
        intro h
        apply hne
        obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.1 h
        exact congrArg (Sigma.mk n)
          ((relCWComplexDiscBundleRelCellEquiv F E A n).symm.injective (eq_of_heq hc))
      have hdisj := pairwiseDisjoint (C := discBundle F E) (mem_univ _) (mem_univ _) hne'
      exact hdisj.preimage _
    disjointBase' := fun n c ↦ by
      rw [coe_discSubtypeMap, image_discSubtypeFun F E A c ball_subset_closedBall,
        discSubtypeBase_eq_preimage]
      exact (disjointBase n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c)).preimage _
    mapsTo := fun n c ↦ by
      obtain ⟨I, hI⟩ := mapsTo (C := discBundle F E) n
        ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c)
      refine ⟨fun k ↦ (I k).image (relCWComplexDiscBundleRelCellEquiv F E A k), ?_⟩
      rw [mapsTo_iff_image_subset, coe_discSubtypeMap,
        image_discSubtypeFun F E A c sphere_subset_closedBall]
      rintro v ⟨x, hx, hxv⟩
      have hv' := hxv ▸ hI hx
      rcases hv' with hvbase | hvcells
      · exact Or.inl (by rw [discSubtypeBase_eq_preimage]; exact hvbase)
      · simp only [mem_iUnion, exists_prop] at hvcells
        obtain ⟨k, hk, i, hiI, hi⟩ := hvcells
        refine Or.inr (mem_iUnion₂.2 ⟨k, hk, mem_iUnion₂.2
          ⟨relCWComplexDiscBundleRelCellEquiv F E A k i, Finset.mem_image_of_mem _ hiI, ?_⟩⟩)
        rw [coe_discSubtypeMap, image_discSubtypeFun F E A _ Subset.rfl]
        simpa using hi
    closed' := fun K _ hK ↦ by
      have hemb : IsClosedEmbedding (Subtype.val : discBundle F E → TotalSpace F E) :=
        .subtypeVal (isClosed_discBundle F E)
      rw [hemb.isClosed_iff_image_isClosed]
      refine RelCWComplex.closed' (C := discBundle F E) (Subtype.val '' K)
        (Subtype.coe_image_subset (discBundle F E) K) ⟨fun n i ↦ ?_, ?_⟩
      · obtain ⟨c, rfl⟩ := (relCWComplexDiscBundleRelCellEquiv F E A n).symm.surjective i
        rw [← image_inter_preimage, ← image_discSubtypeFun F E A c Subset.rfl, ← coe_discSubtypeMap]
        exact hemb.isClosedMap _ (hK.1 n c)
      · rw [← image_inter_preimage, ← discSubtypeBase_eq_preimage]
        exact hemb.isClosedMap _ hK.2
    isClosedBase := by
      rw [discSubtypeBase_eq_preimage]
      exact (isClosedBase (discBundle F E)).preimage continuous_subtypeVal
    union' := by
      ext v
      simp only [mem_union, mem_iUnion, mem_preimage, mem_univ, iff_true,
        coe_discSubtypeMap, image_discSubtypeFun F E A _ Subset.rfl, discSubtypeBase_eq_preimage]
      have hv : v.val ∈ (sphereBundle F E ∪ discBundle F E ∩ TotalSpace.proj ⁻¹' A) ∪
          ⋃ (n : ℕ) (i : cell (discBundle F E) n), closedCell n i := by
        rw [RelCWComplex.union (C := discBundle F E)]
        exact v.property
      simp only [mem_union, mem_iUnion, closedCell] at hv
      rcases hv with hvbase | ⟨n, i, hi⟩
      · exact Or.inl hvbase
      · exact Or.inr ⟨n, relCWComplexDiscBundleRelCellEquiv F E A n i, by simpa using hi⟩ }

/-- The `n`-cells of `relCWComplexDiscBundleSubtypeRel` are the relative `m`-cells of `(B, A)` with
`m + r = n`, where `r` is the rank of the bundle. -/
def relCWComplexDiscBundleSubtypeRelCellEquiv (n : ℕ) :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    cell (univ : Set (discBundle F E)) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  Equiv.refl _

variable {F E A}

/-- Below the rank of the bundle, `relCWComplexDiscBundleSubtypeRel` has no cells. -/
theorem isEmpty_cell_relCWComplexDiscBundleSubtypeRel_of_lt {n : ℕ} (hn : n < Module.finrank ℝ F) :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    IsEmpty (cell (univ : Set (discBundle F E)) n) := by
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  exact ⟨fun c ↦ by
    have := ((relCWComplexDiscBundleSubtypeRelCellEquiv F E A n) c).1.property
    omega⟩

variable {n : ℕ} (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)

/-- The characteristic map of a cell of `relCWComplexDiscBundleSubtypeRel` is `discSubtypeFun`.
This unfolds the `map` field of `relCWComplexDiscBundleSubtypeRel` and
`relCWComplexDiscBundleSubtypeRelCellEquiv`, which is `Equiv.refl`. -/
private theorem coe_map_relCWComplexDiscBundleSubtypeRel :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    ⇑(map n ((relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).symm c)) =
      discSubtypeFun F E A c :=
  coe_discSubtypeMap F E A c

/-- On the closed unit ball, each characteristic map of `relCWComplexDiscBundleSubtypeRel`
coerces to the corresponding characteristic map of `TauCeti.relCWComplexDiscBundleRel`. -/
theorem coe_map_relCWComplexDiscBundleSubtypeRel_of_mem {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    letI := relCWComplexDiscBundleRel F E A
    (map n ((relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).symm c) x : TotalSpace F E) =
      map n ((relCWComplexDiscBundleRelCellEquiv F E A n).symm c) x := by
  rw [coe_map_relCWComplexDiscBundleSubtypeRel]
  exact coe_discSubtypeFun_of_mem F E A c hx

/-- Each characteristic map of `relCWComplexDiscBundleSubtypeRel` projects to the characteristic map
of the underlying base cell on the closed unit ball. -/
theorem proj_map_relCWComplexDiscBundleSubtypeRel {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    discBundleProj F E (map n ((relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).symm c) x) =
      map c.1.val c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1 := by
  rw [discBundleProj_apply, coe_map_relCWComplexDiscBundleSubtypeRel_of_mem c hx]
  exact proj_map_relCWComplexDiscBundleRel c hx

/-- The closed cell of `relCWComplexDiscBundleSubtypeRel` over a relative `m`-cell `j` of `(B, A)`
is `discBundleProj F E ⁻¹' closedCell m j`. -/
@[simp]
theorem closedCell_relCWComplexDiscBundleSubtypeRel :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    closedCell n ((relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).symm c) =
      discBundleProj F E ⁻¹' closedCell c.1.val c.2 := by
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  let _ := relCWComplexDiscBundleRel F E A
  rw [closedCell, coe_map_relCWComplexDiscBundleSubtypeRel,
    image_discSubtypeFun F E A c Subset.rfl, ← closedCell,
    closedCell_relCWComplexDiscBundleRel]
  ext v
  simp [discBundleProj_apply]

/-- The open cell of `relCWComplexDiscBundleSubtypeRel` over a relative `m`-cell `j` of `(B, A)`
consists of the vectors of norm less than one in `D(E)` over `openCell m j`. -/
@[simp]
theorem openCell_relCWComplexDiscBundleSubtypeRel :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    openCell n ((relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).symm c) =
      {v : discBundle F E | ‖(v : TotalSpace F E).snd‖ < 1} ∩
        discBundleProj F E ⁻¹' openCell c.1.val c.2 := by
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  let _ := relCWComplexDiscBundleRel F E A
  rw [openCell, coe_map_relCWComplexDiscBundleSubtypeRel,
    image_discSubtypeFun F E A c ball_subset_closedBall, ← openCell,
    openCell_relCWComplexDiscBundleRel]
  ext v
  simp [discBundleProj_apply]

/-- The boundary of the cell of `relCWComplexDiscBundleSubtypeRel` over a relative `m`-cell `j` of
`(B, A)` is `S(E)` over `closedCell m j` together with `D(E)` over `cellFrontier m j`. -/
@[simp]
theorem cellFrontier_relCWComplexDiscBundleSubtypeRel :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    cellFrontier n ((relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).symm c) =
      Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' closedCell c.1.val c.2 ∪
        discBundleProj F E ⁻¹' cellFrontier c.1.val c.2 := by
  let _ := relCWComplexDiscBundleSubtypeRel F E A
  let _ := relCWComplexDiscBundleRel F E A
  rw [cellFrontier, coe_map_relCWComplexDiscBundleSubtypeRel,
    image_discSubtypeFun F E A c sphere_subset_closedBall, ← cellFrontier,
    cellFrontier_relCWComplexDiscBundleRel]
  ext v
  simp [discBundleProj_apply]

variable (F E A)

/-- `relCWComplexDiscBundleSubtypeRel` is finite-dimensional when `(B, A)` is
finite-dimensional. -/
theorem finiteDimensional_relCWComplexDiscBundleSubtypeRel
    [RelCWComplex.FiniteDimensional (univ : Set B)] :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    RelCWComplex.FiniteDimensional (univ : Set (discBundle F E)) :=
  letI := relCWComplexDiscBundleRel F E A
  haveI := finiteDimensional_relCWComplexDiscBundleRel F E A
  RelCWComplex.finiteDimensional_of_cellEquiv (relCWComplexDiscBundleRel F E A)
    (relCWComplexDiscBundleSubtypeRel F E A) fun n ↦
      (relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).trans
        (relCWComplexDiscBundleRelCellEquiv F E A n).symm

/-- `relCWComplexDiscBundleSubtypeRel` has finite type when `(B, A)` has finite type. -/
theorem finiteType_relCWComplexDiscBundleSubtypeRel [RelCWComplex.FiniteType (univ : Set B)] :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    RelCWComplex.FiniteType (univ : Set (discBundle F E)) :=
  letI := relCWComplexDiscBundleRel F E A
  haveI := finiteType_relCWComplexDiscBundleRel F E A
  RelCWComplex.finiteType_of_cellEquiv (relCWComplexDiscBundleRel F E A)
    (relCWComplexDiscBundleSubtypeRel F E A) fun n ↦
      (relCWComplexDiscBundleSubtypeRelCellEquiv F E A n).trans
        (relCWComplexDiscBundleRelCellEquiv F E A n).symm

/-- `relCWComplexDiscBundleSubtypeRel` is finite when `(B, A)` is finite. -/
theorem finite_relCWComplexDiscBundleSubtypeRel [RelCWComplex.Finite (univ : Set B)] :
    letI := relCWComplexDiscBundleSubtypeRel F E A
    RelCWComplex.Finite (univ : Set (discBundle F E)) :=
  letI := relCWComplexDiscBundleSubtypeRel F E A
  have := finiteDimensional_relCWComplexDiscBundleSubtypeRel F E A
  have := finiteType_relCWComplexDiscBundleSubtypeRel F E A
  finite_of_finiteDimensional_finiteType _

end DiscBundleSubtype

section DiscBundleSubtypeSphereBundle

variable {B : Type u} [TopologicalSpace B] [T2Space B] (F : Type*) [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] (E : B → Type u) [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContinuousFiberNorm F E] [CWComplex (univ : Set B)]

/-- **The disc bundle subtype over a CW complex `B`, relative to the sphere bundle.** If `B` is a
classical CW complex, `discBundle F E` is a classical CW complex on `univ` relative to
`Subtype.val ⁻¹' sphereBundle F E`, with one `(m + r)`-cell for each `m`-cell of `B`
(`TauCeti.relCWComplexDiscBundleSubtypeSphereBundleCellEquiv`). -/
@[instance_reducible]
def relCWComplexDiscBundleSubtypeSphereBundle :
    RelCWComplex (univ : Set (discBundle F E)) (Subtype.val ⁻¹' sphereBundle F E) :=
  (relCWComplexDiscBundleSubtypeRel F E ∅).copy (univ : Set (discBundle F E))
    (Subtype.val ⁻¹' sphereBundle F E) rfl (subtype_sphereBundle_union_empty F E)

/-- The `n`-cells of `relCWComplexDiscBundleSubtypeSphereBundle` are the `m`-cells of `B` with
`m + r = n`, where `r` is the rank of the bundle. -/
def relCWComplexDiscBundleSubtypeSphereBundleCellEquiv (n : ℕ) :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    cell (univ : Set (discBundle F E)) n ≃
      Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m :=
  letI := relCWComplexDiscBundleSubtypeRel F E ∅
  ((relCWComplexDiscBundleSubtypeRel F E ∅).copyCellEquiv (univ : Set (discBundle F E))
    (Subtype.val ⁻¹' sphereBundle F E) rfl (subtype_sphereBundle_union_empty F E) n).trans
    (relCWComplexDiscBundleSubtypeRelCellEquiv F E ∅ n)

variable {F E}

/-- Below the rank of the bundle, `relCWComplexDiscBundleSubtypeSphereBundle` has no cells. -/
theorem isEmpty_cell_relCWComplexDiscBundleSubtypeSphereBundle_of_lt {n : ℕ}
    (hn : n < Module.finrank ℝ F) :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    IsEmpty (cell (univ : Set (discBundle F E)) n) :=
  letI := relCWComplexDiscBundleSubtypeSphereBundle F E
  letI := relCWComplexDiscBundleSubtypeRel F E ∅
  have := isEmpty_cell_relCWComplexDiscBundleSubtypeRel_of_lt (F := F) (E := E) (A := ∅) hn
  ((relCWComplexDiscBundleSubtypeRel F E ∅).copyCellEquiv (univ : Set (discBundle F E))
    (Subtype.val ⁻¹' sphereBundle F E) rfl (subtype_sphereBundle_union_empty F E)
    n).isEmpty_congr.2 inferInstance

variable {n : ℕ} (c : Σ m : {m : ℕ // m + Module.finrank ℝ F = n}, cell (univ : Set B) m)

/-- On the closed unit ball, each characteristic map of `relCWComplexDiscBundleSubtypeSphereBundle`
coerces to the corresponding characteristic map of
`TauCeti.relCWComplexDiscBundleSphereBundle`. -/
theorem coe_map_relCWComplexDiscBundleSubtypeSphereBundle_of_mem {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    letI := relCWComplexDiscBundleSphereBundle F E
    (map n ((relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n).symm c) x :
        TotalSpace F E) =
      map n ((relCWComplexDiscBundleSphereBundleCellEquiv F E n).symm c) x := by
  let I := relCWComplexDiscBundleSubtypeRel F E ∅
  have hcopy := I.map_copy (univ : Set (discBundle F E)) (Subtype.val ⁻¹' sphereBundle F E) rfl
    (subtype_sphereBundle_union_empty F E) n
    ((relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n).symm c)
  refine (congrArg (fun f : PartialEquiv (Fin n → ℝ) (discBundle F E) ↦ (f x : TotalSpace F E))
    hcopy).trans ?_
  rw [relCWComplexDiscBundleSubtypeSphereBundleCellEquiv, Equiv.symm_trans_apply,
    Equiv.apply_symm_apply]
  let _ := relCWComplexDiscBundleRel F E ∅
  rw [coe_map_relCWComplexDiscBundleSubtypeRel_of_mem c hx, coe_map_relCWComplexDiscBundleRel,
    coe_map_relCWComplexDiscBundleSphereBundle]

/-- Each characteristic map of `relCWComplexDiscBundleSubtypeSphereBundle` projects to the
characteristic map of the underlying base cell on the closed unit ball. -/
theorem proj_map_relCWComplexDiscBundleSubtypeSphereBundle {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    discBundleProj F E
        (map n ((relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n).symm c) x) =
      map c.1.val c.2 ((Fin.appendIsometryOfEq c.1.property).symm x).1 := by
  let _ := relCWComplexDiscBundleSphereBundle F E
  rw [discBundleProj_apply, coe_map_relCWComplexDiscBundleSubtypeSphereBundle_of_mem c hx]
  exact proj_map_relCWComplexDiscBundleSphereBundle c hx

/-- The closed cell of `relCWComplexDiscBundleSubtypeSphereBundle` over an `m`-cell `j` of `B` is
`discBundleProj F E ⁻¹' closedCell m j`. -/
@[simp]
theorem closedCell_relCWComplexDiscBundleSubtypeSphereBundle :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    closedCell n ((relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n).symm c) =
      discBundleProj F E ⁻¹' closedCell c.1.val c.2 := by
  let I := relCWComplexDiscBundleSubtypeRel F E ∅
  rw [relCWComplexDiscBundleSubtypeSphereBundleCellEquiv, Equiv.symm_trans_apply]
  refine (I.closedCell_copy (univ : Set (discBundle F E)) (Subtype.val ⁻¹' sphereBundle F E) rfl
    (subtype_sphereBundle_union_empty F E) n _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact closedCell_relCWComplexDiscBundleSubtypeRel (E := E) (A := ∅) c

/-- The open cell of `relCWComplexDiscBundleSubtypeSphereBundle` over an `m`-cell `j` of `B`
consists of the vectors of norm less than one in `D(E)` over `openCell m j`. -/
@[simp]
theorem openCell_relCWComplexDiscBundleSubtypeSphereBundle :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    openCell n ((relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n).symm c) =
      {v : discBundle F E | ‖(v : TotalSpace F E).snd‖ < 1} ∩
        discBundleProj F E ⁻¹' openCell c.1.val c.2 := by
  let I := relCWComplexDiscBundleSubtypeRel F E ∅
  rw [relCWComplexDiscBundleSubtypeSphereBundleCellEquiv, Equiv.symm_trans_apply]
  refine (I.openCell_copy (univ : Set (discBundle F E)) (Subtype.val ⁻¹' sphereBundle F E) rfl
    (subtype_sphereBundle_union_empty F E) n _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact openCell_relCWComplexDiscBundleSubtypeRel (E := E) (A := ∅) c

/-- The boundary of the cell of `relCWComplexDiscBundleSubtypeSphereBundle` over an `m`-cell `j` of
`B` is `S(E)` over `closedCell m j` together with `D(E)` over `cellFrontier m j`. -/
@[simp]
theorem cellFrontier_relCWComplexDiscBundleSubtypeSphereBundle :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    cellFrontier n ((relCWComplexDiscBundleSubtypeSphereBundleCellEquiv F E n).symm c) =
      Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' closedCell c.1.val c.2 ∪
        discBundleProj F E ⁻¹' cellFrontier c.1.val c.2 := by
  let I := relCWComplexDiscBundleSubtypeRel F E ∅
  rw [relCWComplexDiscBundleSubtypeSphereBundleCellEquiv, Equiv.symm_trans_apply]
  refine (I.cellFrontier_copy (univ : Set (discBundle F E)) (Subtype.val ⁻¹' sphereBundle F E) rfl
    (subtype_sphereBundle_union_empty F E) n _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact cellFrontier_relCWComplexDiscBundleSubtypeRel (E := E) (A := ∅) c

variable (F E)

/-- `relCWComplexDiscBundleSubtypeSphereBundle` is finite-dimensional when `B` is
finite-dimensional. -/
theorem finiteDimensional_relCWComplexDiscBundleSubtypeSphereBundle
    [RelCWComplex.FiniteDimensional (univ : Set B)] :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    RelCWComplex.FiniteDimensional (univ : Set (discBundle F E)) :=
  letI := relCWComplexDiscBundleSubtypeRel F E ∅
  haveI := finiteDimensional_relCWComplexDiscBundleSubtypeRel (F := F) (E := E) (A := ∅)
  (relCWComplexDiscBundleSubtypeRel F E ∅).finiteDimensional_copy (univ : Set (discBundle F E))
    (Subtype.val ⁻¹' sphereBundle F E) rfl (subtype_sphereBundle_union_empty F E)

/-- `relCWComplexDiscBundleSubtypeSphereBundle` has finite type when `B` has finite type. -/
theorem finiteType_relCWComplexDiscBundleSubtypeSphereBundle
    [RelCWComplex.FiniteType (univ : Set B)] :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    RelCWComplex.FiniteType (univ : Set (discBundle F E)) :=
  letI := relCWComplexDiscBundleSubtypeRel F E ∅
  haveI := finiteType_relCWComplexDiscBundleSubtypeRel (F := F) (E := E) (A := ∅)
  (relCWComplexDiscBundleSubtypeRel F E ∅).finiteType_copy (univ : Set (discBundle F E))
    (Subtype.val ⁻¹' sphereBundle F E) rfl (subtype_sphereBundle_union_empty F E)

/-- `relCWComplexDiscBundleSubtypeSphereBundle` is finite when `B` is finite. -/
theorem finite_relCWComplexDiscBundleSubtypeSphereBundle [RelCWComplex.Finite (univ : Set B)] :
    letI := relCWComplexDiscBundleSubtypeSphereBundle F E
    RelCWComplex.Finite (univ : Set (discBundle F E)) :=
  letI := relCWComplexDiscBundleSubtypeRel F E ∅
  haveI := finite_relCWComplexDiscBundleSubtypeRel (F := F) (E := E) (A := ∅)
  (relCWComplexDiscBundleSubtypeRel F E ∅).finite_copy (univ : Set (discBundle F E))
    (Subtype.val ⁻¹' sphereBundle F E) rfl (subtype_sphereBundle_union_empty F E)

end DiscBundleSubtypeSphereBundle

end TauCeti
