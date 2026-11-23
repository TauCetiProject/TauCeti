/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# The zero-skeleton of a CW complex

The points of the zero-skeleton correspond to zero-cells. Its topology is discrete, while the
preceding skeleton is empty.
-/

public section

noncomputable section

open Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

/-- The characteristic point of a zero-cell, regarded as a point of the zero-skeleton. -/
def zeroCellPoint (i : cell C 0) : ↑(skeletonLT C ((1 : ℕ) : ℕ∞)) :=
  ⟨map 0 i ![], closedCell_subset_skeletonLT 0 i (by simp [closedCell_zero_eq_singleton])⟩

/-- The point of a zero-cell is the image of the unique point of `Fin 0 → ℝ` under its
characteristic map. -/
@[simp]
theorem coe_zeroCellPoint (i : cell C 0) : (zeroCellPoint C i : X) = map 0 i ![] := (rfl)

/-- Distinct zero-cells have distinct points. -/
theorem zeroCellPoint_injective : Function.Injective (zeroCellPoint C) :=
  fun _ _ h ↦ injective_map_zero C (congrArg Subtype.val h)

/-- The zero-cells are in bijection with the points of the zero-skeleton. -/
def zeroCellEquiv : cell C 0 ≃ ↑(skeletonLT C ((1 : ℕ) : ℕ∞)) :=
  Equiv.ofBijective (zeroCellPoint C) ⟨zeroCellPoint_injective C,
    fun ⟨x, hx⟩ ↦ by
      obtain ⟨m, hm, i, hi⟩ := CWComplex.mem_skeletonLT_iff.mp hx
      obtain rfl : m = 0 := by simpa using hm
      rw [openCell_zero_eq_singleton] at hi
      exact ⟨i, Subtype.ext hi.symm⟩⟩

@[simp]
lemma zeroCellEquiv_apply (i : cell C 0) :
    zeroCellEquiv C i = zeroCellPoint C i := (rfl)

/-- The zero-skeleton has the discrete topology: each of its cells consists of one point. -/
instance zeroSkeletonDiscreteTopology :
    DiscreteTopology (↑(skeletonLT C ((1 : ℕ) : ℕ∞))) := by
  let E : CWComplex.Subcomplex C := skeletonLT C ((1 : ℕ) : ℕ∞)
  refine discreteTopology_iff_forall_isClosed.mpr fun A ↦ ?_
  -- Every subset of `E` is closed, since `E` only has zero-cells, which are points.
  have hc : IsClosed (Subtype.val '' A) :=
    (CWComplex.closed E (Subtype.val '' A) (Subtype.coe_image_subset _ A)).2 fun n j ↦ by
      obtain rfl : n = 0 := by
        rw [CWComplex.Subcomplex.cell_def] at j
        simpa [E, skeletonLT_I] using j.property
      rw [closedCell_zero_eq_singleton]
      exact ((Set.finite_singleton _).subset Set.inter_subset_right).isClosed
  exact Subtype.val_injective.preimage_image A ▸ hc.preimage continuous_subtypeVal

variable {C} in
/-- An open cell containing a point of the zero-skeleton is a zero-cell. -/
lemma eq_zero_of_mem_skeletonLT_one_of_mem_openCell {y : X} (hy : y ∈ skeletonLT C 1) {n : ℕ}
    {j : cell C n} (h : y ∈ openCell n j) : n = 0 := by
  by_contra hn
  exact Set.disjoint_left.1 (CWComplex.disjoint_skeletonLT_openCell
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)) hy h

/-- The stage before the zero-skeleton is empty for an absolute CW complex. -/
instance zeroSkeletonPreviousIsEmpty : IsEmpty (↑(skeletonLT C ((0 : ℕ) : ℕ∞))) :=
  ⟨fun x ↦ by simpa [← SetLike.mem_coe, CWComplex.skeletonLT_zero_eq_empty] using x.property⟩

end TauCeti
