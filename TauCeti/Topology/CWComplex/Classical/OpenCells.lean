/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.PartialHomeomorph.Basic

/-!
# The open cells lying between two consecutive skeleta

The points of a relative CW complex that lie in the `n`-skeleton but not in the `(n-1)`-skeleton
are exactly the points of the open `n`-cells.  This file shows that they form a topological
disjoint union of open unit balls, one for each `n`-cell.

The characteristic map of a cell is, by the definition of a relative CW complex, a bijection of
the open unit ball onto the open cell whose inverse is continuous, hence a homeomorphism onto the
open cell.  The individual open cells are moreover *open* in the difference of the two skeleta:
the complement of one of them there is cut out by the closed set obtained by adjoining all the
remaining closed `n`-cells to the `(n-1)`-skeleton.  Being open, pairwise disjoint and covering,
the open `n`-cells split that difference as a topological sum.

An open cell is in general not open in the complex itself; openness here is relative to the
difference of the two skeleta.

## Main results

* `TauCeti.openCellHomeomorph`: the characteristic map of a cell is a homeomorphism from the open
  unit ball onto the open cell.
* `TauCeti.isClosed_skeletonLT_union_iUnion_closedCell`: adjoining any family of closed `n`-cells
  to the `(n-1)`-skeleton gives a closed set.
* `TauCeti.skeletonLT_succ_diff_skeletonLT`: the difference of two consecutive skeleta is the
  union of the open cells of the top dimension.
* `TauCeti.isOpen_preimage_val_openCell`: each open `n`-cell is open in that union.
* `TauCeti.iUnionOpenCellHomeomorph`: that union is homeomorphic to the disjoint union of one
  open unit ball for each cell of the top dimension.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and the Appendix "Topology of Cell Complexes".
-/

public section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {C D : Set X} [RelCWComplex C D] (n : ℕ)

/-- The target of a characteristic map is the corresponding open cell. -/
@[simp]
lemma target_map_eq_openCell (i : cell C n) : (map n i).target = openCell (C := C) n i := by
  rw [← PartialEquiv.image_source_eq_target, source_eq]
  -- The open cell is by definition the image of the open unit ball.
  rfl

/-- The inverse of a characteristic map sends a point of the open cell into the open unit ball. -/
lemma map_symm_mem_ball {i : cell C n} {x : X} (hx : x ∈ openCell (C := C) n i) :
    (map n i).symm x ∈ ball (0 : Fin n → ℝ) 1 := by
  rw [← source_eq n i]
  exact (map n i).map_target (by rwa [target_map_eq_openCell])

/-- A characteristic map undoes its inverse on the open cell. -/
lemma map_map_symm {i : cell C n} {x : X} (hx : x ∈ openCell (C := C) n i) :
    map n i ((map n i).symm x) = x :=
  (map n i).right_inv (by rwa [target_map_eq_openCell])

/-- **The characteristic map of a cell is a homeomorphism from the open unit ball onto the open
cell.**  Its forward and inverse maps are described by `TauCeti.openCellHomeomorph_apply` and
`TauCeti.openCellHomeomorph_symm_apply`. -/
def openCellHomeomorph (i : cell C n) : ball (0 : Fin n → ℝ) 1 ≃ₜ (openCell (C := C) n i) :=
  -- Restrict the characteristic partial homeomorphism to its source and target.
  (Homeomorph.setCongr (source_eq n i).symm).trans <|
    (PartialHomeomorph.mk (map n i)
        (source_eq n i ▸ (continuousOn n i).mono ball_subset_closedBall)
        (continuousOn_symm n i)).toHomeomorphSourceTarget.trans
      (Homeomorph.setCongr (target_map_eq_openCell n i))

/-- The homeomorphism onto an open cell is the characteristic map. -/
@[simp]
lemma openCellHomeomorph_apply (i : cell C n) (y : ball (0 : Fin n → ℝ) 1) :
    (openCellHomeomorph n i y : X) = map n i y := (rfl)

/-- The inverse of the homeomorphism onto an open cell is the inverse of the characteristic
map. -/
@[simp]
lemma openCellHomeomorph_symm_apply (i : cell C n) (x : (openCell (C := C) n i)) :
    ((openCellHomeomorph n i).symm x : Fin n → ℝ) = (map n i).symm x := (rfl)

variable [T2Space X]

/-- Adjoining any family of closed `n`-cells to the `(n-1)`-skeleton gives a closed set.  Taking
the family of all `n`-cells gives the `n`-skeleton; the point of the general statement is that
omitting some of the cells costs nothing. -/
lemma isClosed_skeletonLT_union_iUnion_closedCell (J : Set (cell C n)) :
    IsClosed ((skeletonLT C (n : ℕ∞) : Set X) ∪ ⋃ j ∈ J, closedCell n j) := by
  set A := (skeletonLT C (n : ℕ∞) : Set X) ∪ ⋃ j ∈ J, closedCell n j with hA
  have hsucc : A ⊆ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
    refine union_subset (skeletonLT_mono (mod_cast n.le_succ)) (iUnion₂_subset fun j _ ↦ ?_)
    exact_mod_cast closedCell_subset_skeletonLT n j
  refine isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    (hsucc.trans (skeletonLT C _).subset_complex) ?_ fun m _ j ↦ ?_
  · rw [inter_eq_right.2 ((skeletonLT C (n : ℕ∞)).base_subset.trans subset_union_left)]
    exact isClosedBase C
  rcases lt_trichotomy m n with hm | rfl | hm
  -- A closed cell of lower dimension lies in the `(n-1)`-skeleton, hence in the set.
  · refine Or.inr ?_
    rw [inter_eq_right.2 (subset_union_left.trans' ((closedCell_subset_skeletonLT m j).trans
      (skeletonLT_mono (mod_cast hm))))]
    exact isClosed_closedCell
  · by_cases hj : j ∈ J
    -- An adjoined closed cell lies in the set.
    · refine Or.inr ?_
      rw [inter_eq_right.2 (subset_union_right.trans' (subset_iUnion₂ j hj))]
      exact isClosed_closedCell
    -- An omitted open cell of dimension `n` misses the skeleton, the frontiers of the adjoined
    -- cells and the adjoined open cells.
    refine Or.inl ?_
    rw [hA, disjoint_union_left]
    refine ⟨disjoint_skeletonLT_openCell le_rfl, disjoint_iUnion₂_left.2 fun k hk ↦ ?_⟩
    rw [← cellFrontier_union_openCell_eq_closedCell, disjoint_union_left]
    exact ⟨(disjoint_skeletonLT_openCell (le_refl (m : ℕ∞))).mono_left
        (cellFrontier_subset_skeletonLT m k),
      disjoint_openCell_of_ne fun hh ↦ hj (eq_of_heq (Sigma.mk.inj_iff.1 hh).2 ▸ hk)⟩
  -- An open cell of higher dimension misses the whole `n`-skeleton.
  · exact Or.inl ((disjoint_skeletonLT_openCell (mod_cast hm)).mono_left hsucc)

/-- **The difference of two consecutive skeleta is the union of the open cells of the top
dimension.** -/
lemma skeletonLT_succ_diff_skeletonLT :
    (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) \ skeletonLT C (n : ℕ∞) =
      ⋃ i : cell C n, openCell (C := C) n i := by
  have hunion : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) =
      (skeletonLT C (n : ℕ∞) : Set X) ∪ ⋃ i : cell C n, openCell (C := C) n i := by
    -- Read both skeleta as the base together with all open cells of lower dimension.
    rw [← iUnion_openCell_eq_skeletonLT, ← iUnion_openCell_eq_skeletonLT, union_assoc]
    congr 1
    simp_rw [Nat.cast_lt]
    exact biUnion_lt_succ _ n
  rw [hunion, union_sdiff_cancel_left]
  exact (disjoint_iUnion_right.2 fun _ ↦ disjoint_skeletonLT_openCell le_rfl).le_bot

/-- A point of `skeletonLT C (n + 1)` that lies in no open `n`-cell lies in `skeletonLT C n`. -/
lemma mem_skeletonLT_of_forall_notMem_openCell {x : X}
    (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X))
    (h : ∀ j : cell C n, x ∉ openCell (C := C) n j) : x ∈ (skeletonLT C (n : ℕ∞) : Set X) := by
  by_contra hxn
  -- Otherwise the point lies in the difference of the two skeleta, hence in an open `n`-cell.
  have hmem : x ∈ ⋃ j : cell C n, openCell (C := C) n j := by
    rw [← skeletonLT_succ_diff_skeletonLT n]
    exact mem_sdiff_of_mem hx hxn
  obtain ⟨j, hj⟩ := mem_iUnion.1 hmem
  exact h j hj

/-- Each open `n`-cell is open in the union of all open `n`-cells: its complement there is cut out
by the closed set obtained by adjoining the remaining closed `n`-cells to the
`(n-1)`-skeleton. -/
lemma isOpen_preimage_val_openCell (i : cell C n) :
    IsOpen (Subtype.val ⁻¹' openCell (C := C) n i :
      Set (⋃ k : cell C n, openCell (C := C) n k : Set X)) := by
  have hcompl : (Subtype.val ⁻¹' openCell (C := C) n i :
      Set (⋃ k : cell C n, openCell (C := C) n k : Set X)) =
      (Subtype.val ⁻¹' ((skeletonLT C (n : ℕ∞) : Set X) ∪
        ⋃ j ∈ ({i}ᶜ : Set (cell C n)), closedCell n j))ᶜ := by
    ext x
    obtain ⟨k, hk⟩ := mem_iUnion.1 x.2
    simp only [mem_preimage, mem_compl_iff, mem_union, not_or, not_exists, mem_iUnion]
    constructor
    · intro hx
      refine ⟨(disjoint_skeletonLT_openCell (le_refl (n : ℕ∞))).notMem_of_mem_right hx, ?_⟩
      rintro j hji hj
      rw [← cellFrontier_union_openCell_eq_closedCell] at hj
      obtain hj | hj := hj
      · exact (disjoint_skeletonLT_openCell (le_refl (n : ℕ∞))).notMem_of_mem_right hx
          (cellFrontier_subset_skeletonLT n j hj)
      · exact (disjoint_openCell_of_ne fun hh ↦
          hji (eq_of_heq (Sigma.mk.inj_iff.1 hh).2)).notMem_of_mem_left hj hx
    · rintro ⟨-, h⟩
      by_cases hki : k = i
      · exact hki ▸ hk
      · exact (h k (by simpa using hki) (openCell_subset_closedCell n k hk)).elim
  rw [hcompl]
  exact ((isClosed_skeletonLT_union_iUnion_closedCell n _).preimage
    continuous_subtype_val).isOpen_compl

/-- **The open `n`-cells form a topological disjoint union of open balls.**  This is a
homeomorphism from the disjoint union of one open unit ball for each `n`-cell onto the union of
the open `n`-cells, which by `TauCeti.skeletonLT_succ_diff_skeletonLT` is the difference of the
`n`-skeleton and the `(n-1)`-skeleton.  Its forward and inverse maps are described by
`TauCeti.iUnionOpenCellHomeomorph_apply` and `TauCeti.iUnionOpenCellHomeomorph_symm_apply`. -/
noncomputable def iUnionOpenCellHomeomorph :
    (Σ _ : cell C n, (ball (0 : Fin n → ℝ) 1)) ≃ₜ
      (⋃ k : cell C n, openCell (C := C) n k : Set X) :=
  -- The characteristic maps are jointly bijective: individual maps are injective on the open
  -- ball, distinct open cells are disjoint, and the open cells cover the target.
  (Equiv.ofBijective
    (fun p : Σ _ : cell C n, (ball (0 : Fin n → ℝ) 1) ↦
      (⟨map n p.1 p.2, mem_iUnion.2 ⟨p.1, p.2, p.2.2, rfl⟩⟩ :
        (⋃ k : cell C n, openCell (C := C) n k : Set X)))
    (by
      constructor
      · rintro ⟨i, y⟩ ⟨j, z⟩ h
        have h' : map n i (y : Fin n → ℝ) = map n j (z : Fin n → ℝ) := congrArg Subtype.val h
        obtain rfl : i = j := by
          by_contra hij
          have hmi : map n i (y : Fin n → ℝ) ∈ openCell (C := C) n i := ⟨y, y.2, rfl⟩
          have hmj : map n i (y : Fin n → ℝ) ∈ openCell (C := C) n j := ⟨z, z.2, h'.symm⟩
          exact (disjoint_openCell_of_ne fun hh ↦
            hij (eq_of_heq (Sigma.mk.inj_iff.1 hh).2)).notMem_of_mem_left hmi hmj
        exact congrArg (Sigma.mk i) (Subtype.ext
          ((map n i).injOn (by rw [source_eq]; exact y.2) (by rw [source_eq]; exact z.2) h'))
      · rintro ⟨x, hx⟩
        obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.1 hx
        exact ⟨⟨i, ⟨y, hy⟩⟩, rfl⟩)).toHomeomorphOfContinuousOpen
    -- Continuity holds on each summand by continuity of its characteristic map.
    (continuous_sigma fun i ↦ Continuous.subtype_mk
      ((continuousOn n i).mono ball_subset_closedBall).domRestrict _)
    -- Each summand embeds onto an open cell, so the assembled map is open.
    (isOpenMap_sigma.2 fun i ↦ by
      -- On the summand `i` the map is `openCellHomeomorph n i` followed by the inclusion of the
      -- open cell `i`, whose range is open in the union.
      have hemb : IsEmbedding fun y : ball (0 : Fin n → ℝ) 1 ↦
          (⟨map n i y, mem_iUnion.2 ⟨i, y, y.2, rfl⟩⟩ :
            (⋃ k : cell C n, openCell (C := C) n k : Set X)) :=
        (IsEmbedding.inclusion (subset_iUnion (fun k ↦ openCell (C := C) n k) i)).comp
          (openCellHomeomorph n i).isEmbedding
      have hrange : (range fun y : ball (0 : Fin n → ℝ) 1 ↦
          (⟨map n i y, mem_iUnion.2 ⟨i, y, y.2, rfl⟩⟩ :
            (⋃ k : cell C n, openCell (C := C) n k : Set X))) =
          Subtype.val ⁻¹' openCell (C := C) n i := by
        ext x
        exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ ⟨y, y.2, rfl⟩, fun ⟨y, hy, hxy⟩ ↦ ⟨⟨y, hy⟩, Subtype.ext hxy⟩⟩
      exact (IsOpenEmbedding.mk hemb (hrange ▸ isOpen_preimage_val_openCell n i)).isOpenMap)

/-- The homeomorphism onto the union of the open `n`-cells is the assembled characteristic map. -/
@[simp]
lemma iUnionOpenCellHomeomorph_apply (p : Σ _ : cell C n, (ball (0 : Fin n → ℝ) 1)) :
    (iUnionOpenCellHomeomorph n p : X) = map n p.1 p.2 := (rfl)

/-- **The inverse of the homeomorphism onto the union of the open `n`-cells.**  A point lying in
the open cell `i` comes from the summand indexed by `i`, with coordinate its image under the
inverse characteristic map of that cell.  This is not a `simp` lemma: the cell `i` is determined
by `x` only through the hypothesis, so `simp` could never instantiate it. -/
lemma iUnionOpenCellHomeomorph_symm_apply {i : cell C n}
    {x : (⋃ k : cell C n, openCell (C := C) n k : Set X)} (hx : (x : X) ∈ openCell (C := C) n i) :
    (iUnionOpenCellHomeomorph n).symm x = ⟨i, ⟨(map n i).symm x, map_symm_mem_ball n hx⟩⟩ := by
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext (map_map_symm n hx).symm

end TauCeti
