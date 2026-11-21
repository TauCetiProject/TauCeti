/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic

/-!
# Codimension skeleta and local isolation

Cells of ambient codimension at least `k` form a subcomplex. Near a relative interior point of
an exact-codimension cell, the support of this skeleton agrees with that cell. One ball avoids
its relative boundary and every other cell in the skeleton, and meets only cells containing it.
This isolates one wall or joint for studying local crossings or small loops around a joint.
The same ball isolates the center in every complementary affine slice, whose dimension is
the cell codimension. No boundedness or salience is required.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Strata.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The subcomplex consisting of all cells of ambient codimension at least `k`.
The dimension inequality also gives the empty complex when `k` exceeds the ambient dimension. -/
noncomputable def codimensionGE (C : FinitePolyhedralComplex h) (k : ℕ) :
    FinitePolyhedralComplex h := by
  classical
  have := h.finiteDimensional
  refine
    { cells := C.cells.filter fun P =>
        Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V
      nonempty := ?_
      rational := ?_
      face_closed := ?_
      inter_face := ?_ }
  · intro P hP
    exact C.nonempty P (Finset.mem_filter.mp hP).1
  · intro P hP
    exact C.rational P (Finset.mem_filter.mp hP).1
  · intro P hP F hF
    obtain ⟨hPC, hdim⟩ := Finset.mem_filter.mp hP
    refine Finset.mem_filter.mpr ⟨C.face_closed P hPC F hF, ?_⟩
    have hle := Submodule.finrank_mono (AffineSubspace.direction_le
      (affineSpan_mono ℝ hF.isExposed.subset))
    exact (Nat.add_le_add_right hle k).trans hdim
  · intro P hP Q hQ hne
    exact C.inter_face P (Finset.mem_filter.mp hP).1 Q (Finset.mem_filter.mp hQ).1 hne

/-- Membership in the codimension subcomplex is the corresponding dimension inequality. -/
@[simp]
theorem mem_cells_codimensionGE {C : FinitePolyhedralComplex h} {k : ℕ} {P : Set V} :
    P ∈ (C.codimensionGE k).cells ↔ P ∈ C.cells ∧
      Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V := by
  classical
  simp [codimensionGE]

/-- The codimension bound zero retains the entire complex. -/
@[simp]
theorem codimensionGE_zero (C : FinitePolyhedralComplex h) :
    C.codimensionGE 0 = C := by
  have := h.finiteDimensional
  apply FinitePolyhedralComplex.ext
  ext P
  simp [Submodule.finrank_le]

/-- Imposing two lower bounds on codimension imposes their maximum. -/
@[simp]
theorem codimensionGE_codimensionGE (C : FinitePolyhedralComplex h) (k l : ℕ) :
    (C.codimensionGE k).codimensionGE l = C.codimensionGE (max k l) := by
  apply FinitePolyhedralComplex.ext
  ext P
  simp only [mem_cells_codimensionGE, ← Nat.add_max_add_left, max_le_iff, and_assoc]

/-- The skeleton retains every exact-codimension stratum at or above its threshold. -/
theorem cellsOfCodimension_codimensionGE_of_le (C : FinitePolyhedralComplex h) {k l : ℕ}
    (hkl : k ≤ l) : (C.codimensionGE k).cellsOfCodimension l = C.cellsOfCodimension l := by
  ext P
  simp only [mem_cellsOfCodimension, mem_cells_codimensionGE]
  exact ⟨fun hP => ⟨hP.1.1, hP.2⟩, fun ⟨hP, hd⟩ => ⟨⟨hP, by omega⟩, hd⟩⟩

/-- At the threshold the exact-codimension cells of the skeleton are those of the complex. -/
@[simp]
theorem cellsOfCodimension_codimensionGE_self (C : FinitePolyhedralComplex h) (k : ℕ) :
    (C.codimensionGE k).cellsOfCodimension k = C.cellsOfCodimension k :=
  C.cellsOfCodimension_codimensionGE_of_le le_rfl

/-- A skeleton has no cells of exact codimension below its threshold. -/
theorem cellsOfCodimension_codimensionGE_of_lt (C : FinitePolyhedralComplex h) {k l : ℕ}
    (hlk : l < k) : (C.codimensionGE k).cellsOfCodimension l = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  obtain ⟨hPk, hPl⟩ := mem_cellsOfCodimension.mp hP
  have hd := (mem_cells_codimensionGE.mp hPk).2
  omega

/-- Every exact-codimension cell belongs to the corresponding codimension subcomplex. -/
theorem cellsOfCodimension_subset_cells_codimensionGE
    (C : FinitePolyhedralComplex h) (k : ℕ) :
    C.cellsOfCodimension k ⊆ (C.codimensionGE k).cells := by
  intro P hP
  obtain ⟨hPC, hdim⟩ := mem_cellsOfCodimension.mp hP
  exact mem_cells_codimensionGE.mpr ⟨hPC, hdim.le⟩

/-- Increasing the codimension bound decreases the set of cells. -/
theorem cells_codimensionGE_antitone (C : FinitePolyhedralComplex h) :
    Antitone (fun k => (C.codimensionGE k).cells) := by
  intro k l hkl P hP
  obtain ⟨hPC, hdim⟩ := mem_cells_codimensionGE.mp hP
  exact mem_cells_codimensionGE.mpr
    ⟨hPC, (Nat.add_le_add_left hkl _).trans hdim⟩

/-- Every codimension skeleton is a subcomplex of the original complex. -/
theorem codimensionGE_isSubcomplex (C : FinitePolyhedralComplex h) (k : ℕ) :
    (C.codimensionGE k).IsSubcomplex C :=
  isSubcomplex_iff.mpr fun _ hP => (mem_cells_codimensionGE.mp hP).1

/-- A complex lies in the skeleton precisely if it is a subcomplex and every cell has
at least the prescribed ambient codimension. -/
theorem isSubcomplex_codimensionGE_iff {C D : FinitePolyhedralComplex h} {k : ℕ} :
    D.IsSubcomplex (C.codimensionGE k) ↔ D.IsSubcomplex C ∧ ∀ P ∈ D.cells,
      Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V := by
  refine ⟨fun hD => ⟨hD.trans (C.codimensionGE_isSubcomplex k), fun P hP =>
    (mem_cells_codimensionGE.mp (isSubcomplex_iff.mp hD hP)).2⟩, ?_⟩
  rintro ⟨hD, hdim⟩
  exact isSubcomplex_iff.mpr fun P hP => mem_cells_codimensionGE.mpr
    ⟨isSubcomplex_iff.mp hD hP, hdim P hP⟩

/-- Raising the threshold gives a subcomplex of the original skeleton. -/
theorem codimensionGE_isSubcomplex_codimensionGE (C : FinitePolyhedralComplex h) {k l : ℕ}
    (hkl : k ≤ l) : (C.codimensionGE l).IsSubcomplex (C.codimensionGE k) :=
  isSubcomplex_iff.mpr (C.cells_codimensionGE_antitone hkl)

/-- Taking the skeleton preserves subcomplex inclusion. -/
theorem IsSubcomplex.codimensionGE {C D : FinitePolyhedralComplex h} (hCD : C.IsSubcomplex D)
    (k : ℕ) : (C.codimensionGE k).IsSubcomplex (D.codimensionGE k) :=
  isSubcomplex_codimensionGE_iff.mpr ⟨(C.codimensionGE_isSubcomplex k).trans hCD,
    fun _ hP => (mem_cells_codimensionGE.mp hP).2⟩

/-- The support of the skeleton lies in the support of the complex. -/
theorem support_codimensionGE_subset (C : FinitePolyhedralComplex h) (k : ℕ) :
    (C.codimensionGE k).support ⊆ C.support :=
  (C.codimensionGE_isSubcomplex k).isWeakRefinement.support_subset

/-- The supports of the skeleta decrease as the codimension bound increases. -/
theorem support_codimensionGE_antitone (C : FinitePolyhedralComplex h) :
    Antitone (fun k => (C.codimensionGE k).support) :=
  fun _ _ hkl => (C.codimensionGE_isSubcomplex_codimensionGE hkl).isWeakRefinement.support_subset

/-- No cells can have codimension greater than the ambient dimension. -/
theorem cells_codimensionGE_eq_empty (C : FinitePolyhedralComplex h) {k : ℕ}
    (hk : Module.finrank ℝ V < k) : (C.codimensionGE k).cells = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  have hdim := (mem_cells_codimensionGE.mp hP).2
  omega

/-- Above the ambient dimension the support of the skeleton is empty. -/
theorem support_codimensionGE_eq_empty (C : FinitePolyhedralComplex h) {k : ℕ}
    (hk : Module.finrank ℝ V < k) : (C.codimensionGE k).support = ∅ := by
  ext x
  simp [mem_support, C.cells_codimensionGE_eq_empty hk]

open Filter Topology in
/-- Near a relative interior point of an exact-codimension cell, each cell of the skeleton
that meets the neighborhood is that cell. -/
theorem eventually_eq_of_mem_cells_codimensionGE (C : FinitePolyhedralComplex h)
    {P : Set V} {k : ℕ} (hP : P ∈ C.cellsOfCodimension k) {x : V}
    (hx : x ∈ intrinsicInterior ℝ P) :
    ∀ᶠ y in 𝓝 x, ∀ Q ∈ (C.codimensionGE k).cells, y ∈ Q → Q = P := by
  obtain ⟨hPC, hdimP⟩ := mem_cellsOfCodimension.mp hP
  filter_upwards [C.eventually_subset_of_mem_intrinsicInterior hPC hx] with y hy Q hQ hyQ
  obtain ⟨hQC, hdimQ⟩ := mem_cells_codimensionGE.mp hQ
  exact (C.eq_of_subset_of_finrank_direction_le hPC hQC (hy Q hQC hyQ) (by omega)).symm

open Filter Topology in
/-- Near a relative interior point of a codimension-`k` cell, the support of the skeleton
of codimension at least `k` agrees with that cell. -/
theorem eventually_mem_support_codimensionGE_iff (C : FinitePolyhedralComplex h)
    {P : Set V} {k : ℕ} (hP : P ∈ C.cellsOfCodimension k) {x : V}
    (hx : x ∈ intrinsicInterior ℝ P) :
    ∀ᶠ y in 𝓝 x, y ∈ (C.codimensionGE k).support ↔ y ∈ P := by
  filter_upwards [C.eventually_eq_of_mem_cells_codimensionGE hP hx] with y hy
  refine ⟨fun hys => ?_, fun hyP =>
    mem_support.mpr ⟨P, C.cellsOfCodimension_subset_cells_codimensionGE k hP, hyP⟩⟩
  obtain ⟨Q, hQ, hyQ⟩ := mem_support.mp hys
  exact hy Q hQ hyQ ▸ hyQ

open Set Filter Topology in
/-- At a relative interior point of an exact-codimension cell, one ball
simultaneously isolates the cell in its skeleton, avoids its relative boundary,
misses every other cell of the skeleton, and meets only cells containing it. -/
theorem exists_ball_inter_support_codimensionGE_eq (C : FinitePolyhedralComplex h)
    {P : Set V} {k : ℕ} (hP : P ∈ C.cellsOfCodimension k) {x : V} (hx : x ∈ intrinsicInterior ℝ P) :
    ∃ r > 0,
      Metric.ball x r ∩ (C.codimensionGE k).support = Metric.ball x r ∩ P ∧
      Disjoint (Metric.ball x r) (intrinsicFrontier ℝ P) ∧
      (∀ Q ∈ (C.codimensionGE k).cells, Q ≠ P → Disjoint (Metric.ball x r) Q) ∧
      ∀ Q ∈ C.cells, (Metric.ball x r ∩ Q).Nonempty → P ⊆ Q := by
  let := h.finiteDimensional
  have hPC := (mem_cellsOfCodimension.mp hP).1
  have hxf : x ∉ intrinsicFrontier ℝ P := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact fun hmem => hmem.2 hx
  have hspan : IsClosed (affineSpan ℝ P : Set V) :=
    (affineSpan ℝ P).isClosed_direction_iff.mp
      (completeSpace_coe_iff_isComplete.mp
        (inferInstance : CompleteSpace (affineSpan ℝ P).direction)).isClosed
  have hfront : ∀ᶠ y in 𝓝 x, y ∉ intrinsicFrontier ℝ P :=
    (isClosed_intrinsicFrontier hspan).isOpen_compl.mem_nhds hxf
  have hnear := (C.eventually_mem_support_codimensionGE_iff hP hx).and
    (hfront.and ((C.eventually_eq_of_mem_cells_codimensionGE hP hx).and
      (C.eventually_subset_of_mem_intrinsicInterior hPC hx)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
  · ext y
    exact and_congr_right fun hy => (hball hy).1
  · exact Set.disjoint_left.mpr fun y hy hyf => (hball hy).2.1 hyf
  · intro Q hQ hne
    apply Set.disjoint_left.mpr
    intro y hy hyQ
    exact hne ((hball hy).2.2.1 Q hQ hyQ)
  · rintro Q hQ ⟨y, hy, hyQ⟩
    exact (hball hy).2.2.2 Q hQ hyQ

/-- At a relative interior point of an exact-codimension cell, one ball isolates
that cell in every supplied complementary affine slice, independently of its choice.
Each slice has the cell's codimension; the ball avoids its relative boundary and
all other skeleton cells and meets only cells containing it.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Joint.lean`, commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0; Mei contributors, author Codex). -/
theorem exists_ball_inter_slice_inter_support_eq_singleton (C : FinitePolyhedralComplex h)
    {P : Set V} {k : ℕ} (hP : P ∈ C.cellsOfCodimension k) {x : V}
    (hx : x ∈ intrinsicInterior ℝ P) :
    ∃ r > 0, Disjoint (Metric.ball x r) (intrinsicFrontier ℝ P) ∧
      (∀ Q ∈ (C.codimensionGE k).cells, Q ≠ P → Disjoint (Metric.ball x r) Q) ∧
      (∀ Q ∈ C.cells, (Metric.ball x r ∩ Q).Nonempty → P ⊆ Q) ∧
      ∀ W : Submodule ℝ V, IsCompl (affineSpan ℝ P).direction W →
        Module.finrank ℝ W = k ∧
        (Metric.ball x r ∩ (AffineSubspace.mk' x W : Set V)) ∩
          (C.codimensionGE k).support = {x} := by
  let := h.finiteDimensional
  obtain ⟨r, hr, hskeleton, hfrontier, hother, hcells⟩ :=
    C.exists_ball_inter_support_codimensionGE_eq hP hx
  refine ⟨r, hr, hfrontier, hother, hcells, ?_⟩
  intro W hW
  have hdimP := (mem_cellsOfCodimension.mp hP).2
  have hdimW := Submodule.finrank_add_eq_of_isCompl hW
  have hxP := intrinsicInterior_subset hx
  have hxA := subset_affineSpan ℝ P hxP
  have hxW : x ∈ (AffineSubspace.mk' x W : Set V) := AffineSubspace.self_mem_mk' x W
  obtain ⟨p, hp⟩ := AffineSubspace.inter_eq_singleton_of_nonempty_of_isCompl
    (s₁ := affineSpan ℝ P) (s₂ := AffineSubspace.mk' x W) ⟨x, hxA⟩ ⟨x, hxW⟩
    (by simpa only [AffineSubspace.direction_mk'] using hW)
  have hxp : x = p := Set.mem_singleton_iff.mp (hp ▸ ⟨hxA, hxW⟩)
  subst p
  refine ⟨by omega, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyball, hyW⟩, hys⟩
    have hyP : y ∈ Metric.ball x r ∩ P := hskeleton ▸ ⟨hyball, hys⟩
    exact hp ▸ ⟨subset_affineSpan ℝ P hyP.2, hyW⟩
  · intro hy
    have hyx := Set.mem_singleton_iff.mp hy
    subst y
    have hxball : x ∈ Metric.ball x r := Metric.mem_ball_self hr
    have hxs : x ∈ Metric.ball x r ∩ (C.codimensionGE k).support :=
      hskeleton.symm ▸ ⟨hxball, hxP⟩
    exact ⟨⟨hxball, hxW⟩, hxs.2⟩

end TauCeti.FinitePolyhedralComplex
