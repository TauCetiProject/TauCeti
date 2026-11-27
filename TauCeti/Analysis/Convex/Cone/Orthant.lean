/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.Convex.Topology

/-!
# Open convex cones containing the positive orthant

An open nonempty convex cone `K` in `ι → ℝ`, with `ι` finite, contains the positive orthant
`{x | ∀ i, 0 < x i}` exactly when every coordinate vector `eᵢ` lies in the closure of `K`
(`ConvexCone.setOf_forall_pos_subset_iff`). If the `eᵢ` lie in the closed convex cone
`closure K`, which contains `0` since `K` is nonempty, so does the open orthant, which then lies
in the interior of `closure K`; that interior is `K`, as `K` is open and convex. Conversely each
`eᵢ` is the limit of `eᵢ + ε • 1` as `ε → 0⁺`, and these points lie in the orthant.
-/

public section

open Filter Topology

namespace ConvexCone

variable {ι : Type*} [Finite ι] [DecidableEq ι]

/-- **Open convex cones containing the positive orthant.** An open nonempty convex cone `K` in
`ι → ℝ` contains the positive orthant if and only if every coordinate vector `eᵢ` lies in the
closure of `K`. -/
theorem setOf_forall_pos_subset_iff {K : ConvexCone ℝ (ι → ℝ)} (hKo : IsOpen (K : Set (ι → ℝ)))
    (hKn : (K : Set (ι → ℝ)).Nonempty) :
    {x : ι → ℝ | ∀ i, 0 < x i} ⊆ K ↔ ∀ i, (Pi.single i 1 : ι → ℝ) ∈ closure (K : Set (ι → ℝ)) := by
  have := Fintype.ofFinite ι
  have hlim {v w : ι → ℝ} : Tendsto (fun ε : ℝ ↦ v + ε • w) (𝓝[>] 0) (𝓝 v) := by
    have hc : Continuous fun ε : ℝ ↦ v + ε • w := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  constructor
  · refine fun h i ↦ mem_closure_of_tendsto (hlim (w := 1)) ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine h fun j ↦ ?_
    by_cases hj : j = i <;> simp [hj, hε, add_pos_of_nonneg_of_pos]
  · intro h x hx
    -- The closure of `K` is a convex cone containing `0`.
    have hzero : (0 : ι → ℝ) ∈ K.closure :=
      Pointed.of_nonempty_of_isClosed (C := K.closure) (by simpa using hKn.closure) isClosed_closure
    -- Every point of the open orthant lies in the closure of `K`, hence in its interior.
    have horth : {x : ι → ℝ | ∀ i, 0 < x i} ⊆ closure K := fun y hy ↦ by
      rw [← Finset.univ_sum_single y]
      refine Finset.sum_induction _ (· ∈ K.closure) (fun _ _ ha hb ↦ K.closure.add_mem ha hb) hzero
        fun i _ ↦ ?_
      have : Pi.single i (y i) = y i • (Pi.single i 1 : ι → ℝ) := by
        ext j
        by_cases hj : j = i <;> simp [hj]
      exact this ▸ K.closure.smul_mem (hy i) (h i)
    have hint : interior (closure (K : Set (ι → ℝ))) = K := by
      rw [K.convex.interior_closure_eq_interior_of_nonempty_interior
        (hKo.interior_eq.symm ▸ hKn), hKo.interior_eq]
    have hopen : IsOpen {x : ι → ℝ | ∀ i, 0 < x i} := by
      simp_rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)
    exact hint ▸ interior_maximal horth hopen hx

end ConvexCone
