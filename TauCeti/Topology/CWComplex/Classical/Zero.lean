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
  ⟨map 0 i ![], closedCell_subset_skeletonLT 0 i (by
    simpa only [Matrix.zero_empty] using map_zero_mem_closedCell 0 i)⟩

/-- The zero-cells are in bijection with the points of the zero-skeleton. -/
def zeroCellEquiv : cell C 0 ≃ ↑(skeletonLT C ((1 : ℕ) : ℕ∞)) :=
  Equiv.ofBijective (zeroCellPoint C) (by
    constructor
    · intro i j h
      exact injective_map_zero C (congrArg Subtype.val h)
    · rintro ⟨x, hx⟩
      have hs : (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X) =
          ⋃ i : cell C 0, closedCell 0 i := by
        simpa [CWComplex.skeletonLT_zero_eq_empty] using
          (skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) 0).symm
      -- The subtype membership is elaborated through the bundled subcomplex, while the
      -- skeleton formula is stated for its underlying set; `change` exposes that set.
      change x ∈ (skeletonLT C ((1 : ℕ) : ℕ∞) : Set X) at hx
      rw [hs] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rw [closedCell_zero_eq_singleton] at hi
      exact ⟨i, Subtype.ext hi.symm⟩)

@[simp]
lemma zeroCellEquiv_apply (i : cell C 0) :
    zeroCellEquiv C i = zeroCellPoint C i := (rfl)

/-- The zero-skeleton has the discrete topology: each of its cells consists of one point. -/
instance zeroSkeletonDiscreteTopology :
    DiscreteTopology (↑(skeletonLT C ((1 : ℕ) : ℕ∞))) := by
  let E : CWComplex.Subcomplex C := skeletonLT C ((1 : ℕ) : ℕ∞)
  have hdegree {n : ℕ} (j : cell (E : Set X) n) : n = 0 := by
    -- A cell of the subcomplex is a cell of `C` whose index lies in `E.I n`.
    change E.I n at j
    have hj : (n : ℕ∞) < ((1 : ℕ) : ℕ∞) := by
      simpa only [E, skeletonLT_I, Set.mem_ofPred_eq] using j.2
    exact Nat.lt_one_iff.mp (by exact_mod_cast hj)
  apply discreteTopology_iff_forall_isClosed.mpr
  intro A
  have hsub : Subtype.val '' A ⊆ (E : Set X) := by
    rintro x ⟨a, -, rfl⟩
    exact a.2
  have hc : IsClosed (Subtype.val '' A) :=
    (CWComplex.closed E (Subtype.val '' A) hsub).2 (by
      intro n j
      have hn := hdegree j
      subst n
      rw [closedCell_zero_eq_singleton]
      exact (Set.finite_singleton _).subset Set.inter_subset_right |>.isClosed)
  have hA : Subtype.val ⁻¹' (Subtype.val '' A) = A :=
    Set.preimage_image_eq A Subtype.val_injective
  exact hA ▸ hc.preimage continuous_subtype_val

/-- The stage before the zero-skeleton is empty for an absolute CW complex. -/
instance zeroSkeletonPreviousIsEmpty : IsEmpty (↑(skeletonLT C ((0 : ℕ) : ℕ∞))) :=
  ⟨fun x ↦ by
    have hx : (x.1 : X) ∈ (skeletonLT C (0 : ℕ∞) : Set X) := x.2
    rw [CWComplex.skeletonLT_zero_eq_empty] at hx
    exact False.elim hx⟩

end TauCeti
