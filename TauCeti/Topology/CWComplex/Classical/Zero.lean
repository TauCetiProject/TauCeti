/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Subcomplex
import TauCeti.Topology.CWComplex.Classical.Skeleton.Compression

/-!
# The zero-skeleton of a CW complex

The points of the zero-skeleton correspond to zero-cells. Its topology is discrete, while the
preceding skeleton is empty. For any nonempty relative CW complex, the zero-skeleton is nonempty
(`TauCeti.zeroSkeletonNonempty`, `TauCeti.nonempty_skeletonLT_one`).
-/

public section

noncomputable section

open Topology Topology.RelCWComplex

universe w

namespace TauCeti

section RelCWComplex

variable {X : Type w} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]

/-- The zero-skeleton of a nonempty relative CW complex is nonempty: every point of the complex is
joined to it by a path (`TauCeti.exists_joined_skeletonLT`). -/
theorem nonempty_skeletonLT_one (hC : C.Nonempty) : (skeletonLT C 1 : Set X).Nonempty := by
  obtain ⟨x, hx⟩ := hC
  obtain ⟨a, -⟩ := exists_joined_skeletonLT (C := C) (n := 0) (by simp)
    (skeletonLT C ((1 : ℕ) : ℕ∞)).subset_complex ⟨x, hx⟩
  exact ⟨a.1, a.2⟩

/-- The zero-skeleton of a nonempty relative CW complex is a nonempty type. -/
instance zeroSkeletonNonempty [Nonempty C] : Nonempty (↑(skeletonLT C ((1 : ℕ) : ℕ∞))) :=
  let ⟨x⟩ := ‹Nonempty C›
  (nonempty_skeletonLT_one (C := C) ⟨x.1, x.2⟩).to_subtype

end RelCWComplex

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

/-- The characteristic point of a zero-cell, regarded as a point of the zero-skeleton. -/
def zeroCellPoint (i : cell C 0) : ↑(skeletonLT C ((1 : ℕ) : ℕ∞)) :=
  ⟨map 0 i ![], closedCell_subset_skeletonLT 0 i (by simp [closedCell_zero_eq_singleton])⟩

/-- The zero-cells are in bijection with the points of the zero-skeleton. -/
def zeroCellEquiv : cell C 0 ≃ ↑(skeletonLT C ((1 : ℕ) : ℕ∞)) :=
  Equiv.ofBijective (zeroCellPoint C) ⟨fun _ _ h ↦ injective_map_zero C (congrArg Subtype.val h),
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
        simpa [E, skeletonLT_I] using j.2
      rw [closedCell_zero_eq_singleton]
      exact ((Set.finite_singleton _).subset Set.inter_subset_right).isClosed
  exact Subtype.val_injective.preimage_image A ▸ hc.preimage continuous_subtype_val

/-- The stage before the zero-skeleton is empty for an absolute CW complex. -/
instance zeroSkeletonPreviousIsEmpty : IsEmpty (↑(skeletonLT C ((0 : ℕ) : ℕ∞))) :=
  ⟨fun x ↦ by simpa [← SetLike.mem_coe, CWComplex.skeletonLT_zero_eq_empty] using x.2⟩

end TauCeti
