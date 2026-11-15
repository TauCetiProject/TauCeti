/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Closures of strict affine cuts

A nonempty cut of a closed convex set by continuous strict affine inequalities
has closure equal to the corresponding weak cut. The inequalities may form an
infinite family. This computes closures of locally closed polyhedra.

Adapted from `Mei/Analysis/Convex/Halfspace.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

open Set

/-- A nonempty cut of a closed convex set by strict continuous affine inequalities has
as closure the cut by the weakened inequalities. Nonemptiness is essential: in `ℝ`, the
cut of `{x | x ≤ 0}` by `-x < 0` is empty, while the weak cut is `{0}`. -/
theorem Convex.closure_inter_setOf_forall_neg {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {P : Set V}
    (hP : Convex ℝ P) (hPc : IsClosed P) (g : ι → V →ᴬ[ℝ] ℝ)
    (hne : (P ∩ {x | ∀ k, g k x < 0}).Nonempty) :
    closure (P ∩ {x | ∀ k, g k x < 0}) = P ∩ {x | ∀ k, g k x ≤ 0} := by
  have hclosed : IsClosed (P ∩ {x | ∀ k, g k x ≤ 0}) := by
    rw [Set.ofPred_forall]
    exact hPc.inter (isClosed_iInter fun k => isClosed_Iic.preimage (g k).continuous)
  apply Subset.antisymm
  · exact closure_minimal (inter_subset_inter_right _ fun x hx k => (hx k).le) hclosed
  · obtain ⟨p, hpP, hpg⟩ := hne
    rintro x ⟨hxP, hxg⟩
    have hs : openSegment ℝ x p ⊆ P ∩ {x | ∀ k, g k x < 0} := by
      rintro y ⟨a, b, ha, hb, hab, rfl⟩
      refine ⟨hP hxP hpP ha.le hb.le hab, fun k => ?_⟩
      have he : g k (a • x + b • p) = a * g k x + b * g k p :=
        Convex.combo_affine_apply (f := (g k).toAffineMap) hab
      rw [he]
      exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le (hxg k))
        (mul_neg_of_pos_of_neg hb (hpg k))
    exact closure_mono hs (segment_subset_closure_openSegment (left_mem_segment ℝ x p))
