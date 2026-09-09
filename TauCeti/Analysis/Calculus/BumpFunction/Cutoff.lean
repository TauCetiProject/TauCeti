/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Opens
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth cutoffs for compact subsets

This module provides smooth, compactly supported cutoffs for compact subsets of a
finite-dimensional real normed space. The cutoff is equal to one on a neighborhood of the compact
set and has topological support in a prescribed open set, which is the localization step used for
compact exhaustions in domain arguments.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.
-/

public section

open Function Set TopologicalSpace
open scoped ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A compact set contained in an open set admits a smooth cutoff equal to one on a neighborhood
of the compact set.

The cutoff takes values in `[0, 1]`, has compact support, and its topological support is contained
in the prescribed open set. -/
theorem _root_.IsCompact.exists_contDiff_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ ψ : E → ℝ,
      ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        K ⊆ interior (ψ ⁻¹' {1}) ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U := by
  obtain ⟨L, hL, hL_closed, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨f, hfK, hfL, hf_range⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (modelWithCornersSelf ℝ E)
      hK.isClosed hKL (n := (⊤ : ℕ∞))
  let ψ : E → ℝ := f
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    dsimp [ψ]
    exact f.contMDiff.contDiff
  have hψ_eq_one_nhds : K ⊆ interior (ψ ⁻¹' {1}) := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_nhdsSet_iff_forall.mp hfK x hx
  have hψ_support : support ψ ⊆ L := by
    intro x hx
    by_contra hnot
    exact hx (hfL x hnot)
  have hψ_compact : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact hL hψ_support
  have hψ_tsupp : tsupport ψ ⊆ U := by
    rw [tsupport]
    exact (closure_minimal hψ_support hL_closed).trans hLU
  have hψ_range : range ψ ⊆ Icc 0 1 := by
    rintro y ⟨x, rfl⟩
    exact hf_range x
  exact ⟨ψ, hψ_smooth, hψ_range, hψ_eq_one_nhds, hψ_compact, hψ_tsupp⟩

/-- A compact-exhaustion term in an open set admits a smooth cutoff supported in the interior of
the next term. -/
theorem _root_.CompactExhaustion.exists_contDiff_cutoff {Omega : Opens E}
    (K : CompactExhaustion Omega) (n : ℕ) :
    ∃ ψ : E → ℝ,
      ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        EqOn ψ 1 ((Subtype.val : Omega → E) '' K n) ∧
        (Subtype.val : Omega → E) '' K n ⊆ interior (ψ ⁻¹' {1}) ∧
        HasCompactSupport ψ ∧
          tsupport ψ ⊆ (Subtype.val : Omega → E) '' interior (K (n + 1)) := by
  have hK : IsCompact ((Subtype.val : Omega → E) '' K n) :=
    (K.isCompact n).image continuous_subtype_val
  have hU : IsOpen ((Subtype.val : Omega → E) '' interior (K (n + 1))) :=
    Omega.isOpen.isOpenMap_subtype_val _ isOpen_interior
  have hKU :
      (Subtype.val : Omega → E) '' K n ⊆ (Subtype.val : Omega → E) '' interior (K (n + 1)) :=
    image_mono (K.subset_interior_succ n)
  obtain ⟨ψ, hψ_smooth, hψ_range, hψ_eq_one_nhds, hψ_compact, hψ_tsupp⟩ :=
    hK.exists_contDiff_cutoff hU hKU
  have hψ_eq_one : EqOn ψ 1 ((Subtype.val : Omega → E) '' K n) := by
    intro x hx
    simpa only [mem_preimage, mem_singleton_iff, Pi.one_apply] using
      interior_subset (hψ_eq_one_nhds hx)
  exact ⟨ψ, hψ_smooth, hψ_range, hψ_eq_one, hψ_eq_one_nhds, hψ_compact, hψ_tsupp⟩

end TauCeti
