/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Compactness of convex hulls in finite dimension

In a finite-dimensional topological vector space over an ordered field with compact closed
intervals, such as `ℝ`, the convex hull of a compact set is compact. By Carathéodory's theorem
(`eq_pos_convex_span_of_mem_convexHull`) every point of the convex hull of `s` is a convex
combination of at most `d + 1` points of `s`, where `d` is the dimension, so the convex hull is
the image of the compact set of pairs of weights in the standard simplex and `(d + 1)`-tuples of
points of `s` under the continuous map `(w, z) ↦ ∑ i, w i • z i`.

This is what makes convex separation arguments in finite dimension produce exact convex
combinations: a point outside the convex hull of a compact set is outside a closed convex set,
so it can be separated from it by a continuous linear functional.

In infinite dimension the convex hull of a compact set need not even be closed.

## Main results

* `IsCompact.convexHull`: in finite dimension, the convex hull of a compact set is compact.
-/

public section

open Set Module Function

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [IsTopologicalRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

/-- In a finite-dimensional topological vector space, the convex hull of a compact set is
compact. -/
theorem IsCompact.convexHull {s : Set E} (hs : IsCompact s) : IsCompact (convexHull 𝕜 s) := by
  classical
  -- The convex combinations of `m = d + 1` points of `s`, with their weights, form a compact set.
  set m := finrank 𝕜 E + 1
  set K : Set ((Fin m → 𝕜) × (Fin m → E)) :=
    (univ.pi (fun _ ↦ Icc 0 1) ×ˢ univ.pi (fun _ ↦ s)) ∩ {p | ∑ i, p.1 i = 1}
  have hK : IsCompact K :=
    ((isCompact_univ_pi fun _ ↦ isCompact_Icc).prod (isCompact_univ_pi fun _ ↦ hs)).inter_right
      (isClosed_eq (by fun_prop) continuous_const)
  suffices _root_.convexHull 𝕜 s = (fun p ↦ ∑ i, p.1 i • p.2 i) '' K from
    this ▸ hK.image (by fun_prop)
  refine subset_antisymm (fun x hx ↦ ?_) ?_
  · -- By Carathéodory, `x` is a positive convex combination of affinely independent points of `s`,
    -- of which there are at most `m`; pad the family to `Fin m` by zero weights.
    obtain ⟨ι, _, z, w, hzs, hz, hw₀, hw₁, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hx
    obtain ⟨i₀⟩ : Nonempty ι := by
      by_contra h
      simp [not_nonempty_iff.1 h] at hw₁
    have hcard : Fintype.card ι ≤ Fintype.card (Fin m) := by
      rw [Fintype.card_fin]
      exact hz.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
    have hw_le (i : ι) : w i ≤ 1 :=
      hw₁ ▸ Finset.single_le_sum (fun j _ ↦ (hw₀ j).le) (Finset.mem_univ i)
    refine ⟨(extend g w 0, extend g z fun _ ↦ z i₀), ⟨⟨fun j _ ↦ ?_, fun j _ ↦ ?_⟩, ?_⟩, ?_⟩
    · dsimp only
      by_cases hj : ∃ i, g i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [g.injective.extend_apply]
        exact ⟨(hw₀ i).le, hw_le i⟩
      · rw [extend_apply' _ _ _ hj]
        exact ⟨le_rfl, zero_le_one⟩
    · dsimp only
      by_cases hj : ∃ i, g i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [g.injective.extend_apply]
        exact hzs (mem_range_self i)
      · rw [extend_apply' _ _ _ hj]
        exact hzs (mem_range_self i₀)
    · rw [mem_ofPred_eq, ← hw₁]
      exact (Fintype.sum_of_injective g g.injective w (extend g w 0)
        (fun j hj ↦ extend_apply' w (0 : Fin m → 𝕜) j hj)
        fun i ↦ (g.injective.extend_apply w 0 i).symm).symm
    · exact (Fintype.sum_of_injective g g.injective (fun i ↦ w i • z i)
        (fun j ↦ extend g w 0 j • extend g z (fun _ ↦ z i₀) j)
        (fun j hj ↦ by simp only [extend_apply' w (0 : Fin m → 𝕜) j hj, Pi.zero_apply, zero_smul])
        fun i ↦ by simp only [g.injective.extend_apply]).symm
  · rintro _ ⟨p, ⟨⟨hp₀, hps⟩, hp₁⟩, rfl⟩
    exact (convex_convexHull 𝕜 s).sum_mem (fun i _ ↦ (hp₀ i (mem_univ i)).1) hp₁
      fun i _ ↦ subset_convexHull 𝕜 s (hps i (mem_univ i))
