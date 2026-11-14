/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic

/-!
# Codimension skeleta and local isolation

The cells of ambient codimension at least `k` form a subcomplex. Near a relative
interior point of an exact-codimension cell, this skeleton is precisely that
cell: one ball also avoids its boundary and all other cells of the same codimension,
and meets only cells containing it. No boundedness or salience is required.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Strata.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).
Dimension rigidity reuses the existing intrinsic-interior dimension theorem.
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The subcomplex consisting of all cells of ambient codimension at least `k`.
The dimension inequality also gives the empty complex when `k` exceeds the ambient dimension. -/
noncomputable def codimensionAtLeast (C : FinitePolyhedralComplex h) (k : ℕ) :
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
theorem mem_cells_codimensionAtLeast (C : FinitePolyhedralComplex h) (k : ℕ) (P : Set V) :
    P ∈ (C.codimensionAtLeast k).cells ↔ P ∈ C.cells ∧
      Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V := by
  classical
  simp [codimensionAtLeast]

/-- The codimension bound zero retains the entire complex. -/
@[simp]
theorem codimensionAtLeast_zero (C : FinitePolyhedralComplex h) :
    C.codimensionAtLeast 0 = C := by
  have := h.finiteDimensional
  apply FinitePolyhedralComplex.ext
  ext P
  simp [Submodule.finrank_le]

/-- Every exact-codimension cell belongs to the corresponding codimension subcomplex. -/
theorem cellsOfCodimension_subset_cells_codimensionAtLeast
    (C : FinitePolyhedralComplex h) (k : ℕ) :
    C.cellsOfCodimension k ⊆ (C.codimensionAtLeast k).cells := by
  intro P hP
  obtain ⟨hPC, hdim⟩ := mem_cellsOfCodimension.mp hP
  exact (C.mem_cells_codimensionAtLeast k P).mpr ⟨hPC, hdim.le⟩

/-- Increasing the codimension bound gives a subcomplex of the previous one. -/
theorem cells_codimensionAtLeast_antitone (C : FinitePolyhedralComplex h) :
    Antitone (fun k => (C.codimensionAtLeast k).cells) := by
  intro k l hkl P hP
  obtain ⟨hPC, hdim⟩ := (C.mem_cells_codimensionAtLeast l P).mp hP
  exact (C.mem_cells_codimensionAtLeast k P).mpr
    ⟨hPC, (Nat.add_le_add_left hkl _).trans hdim⟩

/-- Every codimension skeleton is a subcomplex of the original complex. -/
theorem codimensionAtLeast_isSubcomplex (C : FinitePolyhedralComplex h) (k : ℕ) :
    (C.codimensionAtLeast k).IsSubcomplex C :=
  isSubcomplex_iff.mpr fun _ hP => ((C.mem_cells_codimensionAtLeast k _).mp hP).1

/-- No cells can have codimension greater than the ambient dimension. -/
theorem cells_codimensionAtLeast_eq_empty (C : FinitePolyhedralComplex h) {k : ℕ}
    (hk : Module.finrank ℝ V < k) : (C.codimensionAtLeast k).cells = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro P hP
  have hdim := ((C.mem_cells_codimensionAtLeast k P).mp hP).2
  omega

open Filter Topology in
/-- Near a relative interior point of a codimension-`k` cell, the skeleton of
codimension at least `k` agrees with that cell. -/
theorem eventually_mem_support_codimensionAtLeast_iff (C : FinitePolyhedralComplex h)
    {P : Set V} {k : ℕ} (hP : P ∈ C.cellsOfCodimension k) {x : V}
    (hx : x ∈ intrinsicInterior ℝ P) :
    ∀ᶠ y in 𝓝 x, y ∈ (C.codimensionAtLeast k).support ↔ y ∈ P := by
  let := h.finiteDimensional
  obtain ⟨hPC, hdimP⟩ := mem_cellsOfCodimension.mp hP
  filter_upwards [C.eventually_subset_of_mem_intrinsicInterior hPC hx] with y hy
  constructor
  · intro hys
    obtain ⟨Q, hQ, hyQ⟩ := mem_support.mp hys
    obtain ⟨hQC, hdimQ⟩ := (C.mem_cells_codimensionAtLeast k Q).mp hQ
    have hPQ := hy Q hQC hyQ
    have hle := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hPQ))
    have heq : P = Q := C.eq_of_subset_of_finrank_direction_eq hPC hQC hPQ (by omega)
    exact heq ▸ hyQ
  · intro hyP
    exact mem_support.mpr ⟨P, C.cellsOfCodimension_subset_cells_codimensionAtLeast k hP, hyP⟩

open Set Filter Topology in
/-- At a relative interior point of an exact-codimension cell, one ball
simultaneously isolates the cell in its skeleton, avoids its relative boundary,
misses every other cell of the same codimension, and meets only cells containing it. -/
theorem exists_isolating_ball (C : FinitePolyhedralComplex h) {P : Set V} {k : ℕ}
    (hP : P ∈ C.cellsOfCodimension k) {x : V} (hx : x ∈ intrinsicInterior ℝ P) :
    ∃ r > 0,
      Metric.ball x r ∩ (C.codimensionAtLeast k).support = Metric.ball x r ∩ P ∧
      Disjoint (Metric.ball x r) (intrinsicFrontier ℝ P) ∧
      (∀ Q ∈ C.cellsOfCodimension k, Q ≠ P → Disjoint (Metric.ball x r) Q) ∧
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
  have hnear := (C.eventually_mem_support_codimensionAtLeast_iff hP hx).and
    (hfront.and (C.eventually_subset_of_mem_intrinsicInterior hPC hx))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, hr, ?_, ?_, ?_, ?_⟩
  · ext y
    exact and_congr_right fun hy => (hball hy).1
  · exact Set.disjoint_left.mpr fun y hy hyf => (hball hy).2.1 hyf
  · intro Q hQ hne
    apply Set.disjoint_left.mpr
    intro y hy hyQ
    obtain ⟨hQC, hdimQ⟩ := mem_cellsOfCodimension.mp hQ
    have hPQ := (hball hy).2.2 Q hQC hyQ
    have hdimP := (mem_cellsOfCodimension.mp hP).2
    have heq : P = Q := C.eq_of_subset_of_finrank_direction_eq hPC hQC hPQ (by omega)
    exact hne heq.symm
  · rintro Q hQ ⟨y, hy, hyQ⟩
    exact (hball hy).2.2 Q hQ hyQ

end TauCeti.FinitePolyhedralComplex
