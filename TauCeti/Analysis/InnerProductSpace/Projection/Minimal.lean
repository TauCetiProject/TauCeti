/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nested convex projections and norm-convergent tail convex combinations in Hilbert spaces

Let `K : ℕ → Set E` be a decreasing sequence of convex subsets of a real inner product space `E`,
and let `p n ∈ K n` minimize the distance `‖u - w‖` to a fixed point `u : E` over `w ∈ K n`. When
the distances `‖u - p n‖` are bounded above, the parallelogram identity gives
`‖p m - p n‖ ^ 2 ≤ 2 * (‖u - p n‖ ^ 2 - ‖u - p m‖ ^ 2)` for `m ≤ n`, so `p` is a Cauchy sequence.

Applying this at `u = 0` to the closed tail convex hulls `closure (convexHull ℝ (f '' Set.Ici n))`
of a bounded sequence `f : ℕ → E` in a complete real inner product space yields a Hilbert-space form
of Mazur's lemma without passing through the weak topology: there exists a sequence `w : ℕ → E` of
finite tail convex combinations `w n ∈ convexHull ℝ (f '' Set.Ici n)` that converges in norm.

## Main results

* `TauCeti.cauchySeq_of_antitone_convex_norm_sub_le`: metric projections onto a decreasing sequence
  of convex sets with bounded distances form a Cauchy sequence.
* `TauCeti.exists_tendsto_of_antitone_isClosed_convex_norm_sub_le`: in a complete real inner product
  space, those metric projections converge in norm to a point of `⋂ n, K n`.
* `TauCeti.exists_tendsto_mem_convexHull_image_Ici`: every bounded sequence in a complete real inner
  product space admits a norm-convergent sequence of finite tail convex combinations.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let `K : ℕ → Set E` be a decreasing sequence of convex sets in a real inner product space, and
suppose `p n ∈ K n` minimizes `‖u - w‖` over `w ∈ K n`. If the minimal distances `‖u - p n‖` are
bounded above, then `p` is a Cauchy sequence. -/
theorem cauchySeq_of_antitone_convex_norm_sub_le {K : ℕ → Set E} (hanti : Antitone K)
    (hconv : ∀ n, Convex ℝ (K n)) {u : E} {p : ℕ → E} (hp_mem : ∀ n, p n ∈ K n)
    (hp_min : ∀ n, ∀ w ∈ K n, ‖u - p n‖ ≤ ‖u - w‖)
    (hbdd : BddAbove (range fun n ↦ ‖u - p n‖)) :
    CauchySeq p := by
  let d : ℕ → ℝ := fun n ↦ ‖u - p n‖ ^ 2
  have hd_mono : Monotone d := fun m n hmn ↦
    pow_le_pow_left₀ (norm_nonneg _) (hp_min m (p n) (hanti hmn (hp_mem n))) 2
  have hd_bdd : BddAbove (range d) := by
    obtain ⟨C, hC⟩ := hbdd
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC ⟨0, rfl⟩)
    exact ⟨C ^ 2, forall_mem_range.2 fun n ↦
      pow_le_pow_left₀ (norm_nonneg _) (hC ⟨n, rfl⟩) 2⟩
  have hd_cauchy : CauchySeq d := (tendsto_atTop_ciSup hd_mono hd_bdd).cauchySeq
  have hpar {m n : ℕ} (hmn : m ≤ n) : ‖p m - p n‖ ^ 2 ≤ 2 * (d n - d m) := by
    have hmid_mem : (2 : ℝ)⁻¹ • (p m + p n) ∈ K m := by
      rw [smul_add]
      exact hconv m (hp_mem m) (hanti hmn (hp_mem n)) (by positivity) (by positivity) (by ring)
    have hmid_le : ‖u - p m‖ ≤ ‖u - (2 : ℝ)⁻¹ • (p m + p n)‖ := hp_min m _ hmid_mem
    have htwo_mid : (2 : ℝ) • (u - (2 : ℝ)⁻¹ • (p m + p n)) = (u - p n) + (u - p m) := by
      have htwo : (2 : ℝ) * (2 : ℝ)⁻¹ = 1 := by ring
      rw [smul_sub, smul_smul, htwo, one_smul, two_smul ℝ u]
      abel
    have hsum_norm : 2 * ‖u - p m‖ ≤ ‖(u - p n) + (u - p m)‖ := by
      calc
        2 * ‖u - p m‖ ≤ 2 * ‖u - (2 : ℝ)⁻¹ • (p m + p n)‖ := by gcongr
        _ = ‖(2 : ℝ) • (u - (2 : ℝ)⁻¹ • (p m + p n))‖ := by
          rw [norm_smul, Real.norm_of_nonneg zero_le_two]
        _ = ‖(u - p n) + (u - p m)‖ := by rw [htwo_mid]
    have hsum_sq : 4 * d m ≤ ‖(u - p n) + (u - p m)‖ ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hsum_norm 2
      linarith
    have hdiff : (u - p n) - (u - p m) = p m - p n := by abel
    have hplaw := parallelogram_law_with_norm ℝ (u - p n) (u - p m)
    rw [hdiff] at hplaw
    linarith
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hd_cauchy (ε ^ 2 / 2) (by positivity)
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hsq_lt : dist (p m) (p n) ^ 2 < ε ^ 2 := by
    rcases le_total m n with hmn | hnm
    · rw [dist_eq_norm]
      have hdm : d n - d m ≤ dist (d m) (d n) := by
        rw [Real.dist_eq, abs_sub_comm]
        exact le_abs_self _
      linarith [hpar hmn, hN m hm n hn]
    · rw [dist_comm, dist_eq_norm]
      have hdn : d m - d n ≤ dist (d n) (d m) := by
        rw [Real.dist_eq, abs_sub_comm]
        exact le_abs_self _
      linarith [hpar hnm, hN n hn m hm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq_lt

section Complete

variable [CompleteSpace E]

/-- In a complete real inner product space, metric projections onto a decreasing sequence of closed
convex sets with bounded distances converge in norm to a point of the intersection `⋂ n, K n`. -/
theorem exists_tendsto_of_antitone_isClosed_convex_norm_sub_le {K : ℕ → Set E}
    (hanti : Antitone K) (hclosed : ∀ n, IsClosed (K n)) (hconv : ∀ n, Convex ℝ (K n)) {u : E}
    {p : ℕ → E} (hp_mem : ∀ n, p n ∈ K n)
    (hp_min : ∀ n, ∀ w ∈ K n, ‖u - p n‖ ≤ ‖u - w‖)
    (hbdd : BddAbove (range fun n ↦ ‖u - p n‖)) :
    ∃ v ∈ ⋂ n, K n, Tendsto p atTop (𝓝 v) := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_antitone_convex_norm_sub_le hanti hconv hp_mem hp_min hbdd)
  refine ⟨v, mem_iInter.2 fun n ↦ ?_, hv⟩
  exact (hclosed n).mem_of_tendsto hv
    ((eventually_ge_atTop n).mono fun m hm ↦ hanti hm (hp_mem m))

/-- **Norm-convergent tail convex combinations in a Hilbert space.** Every bounded sequence
`f : ℕ → E` in a complete real inner product space admits a vector `v : E` and a sequence
`w : ℕ → E` of finite convex combinations `w n ∈ convexHull ℝ (f '' Set.Ici n)` such that `w`
converges to `v` in norm. -/
theorem exists_tendsto_mem_convexHull_image_Ici {f : ℕ → E}
    (hbdd : Bornology.IsBounded (range f)) :
    ∃ (v : E) (w : ℕ → E), (∀ n, w n ∈ convexHull ℝ (f '' Ici n)) ∧
      Tendsto w atTop (𝓝 v) := by
  let K : ℕ → Set E := fun n ↦ closure (convexHull ℝ (f '' Ici n))
  have hK_anti : Antitone K := fun m n hmn ↦
    closure_mono (convexHull_mono (image_mono (Ici_subset_Ici.2 hmn)))
  have hK_ne (n : ℕ) : (K n).Nonempty :=
    ⟨f n, subset_closure (subset_convexHull ℝ _ ⟨n, self_mem_Ici, rfl⟩)⟩
  have hK_closed (n : ℕ) : IsClosed (K n) := isClosed_closure
  have hK_conv (n : ℕ) : Convex ℝ (K n) := (convex_convexHull ℝ _).closure
  choose p hp_mem hp_eq using fun n ↦
    exists_norm_eq_iInf_of_complete_convex (hK_ne n) (hK_closed n).isComplete (hK_conv n) 0
  have hp_min (n : ℕ) (w : E) (hw : w ∈ K n) : ‖(0 : E) - p n‖ ≤ ‖(0 : E) - w‖ := by
    rw [hp_eq n]
    exact ciInf_le ⟨0, forall_mem_range.2 fun _ ↦ norm_nonneg _⟩ (⟨w, hw⟩ : K n)
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hbdd
  have hp_bdd : BddAbove (range fun n ↦ ‖(0 : E) - p n‖) := by
    refine ⟨C, forall_mem_range.2 fun n ↦ ?_⟩
    have hfn : f n ∈ K n := subset_closure (subset_convexHull ℝ _ ⟨n, self_mem_Ici, rfl⟩)
    have hfnC : ‖f n‖ ≤ C := by simpa using hC (mem_range_self n)
    calc
      ‖(0 : E) - p n‖ ≤ ‖(0 : E) - f n‖ := hp_min n (f n) hfn
      _ = ‖f n‖ := by simp
      _ ≤ C := hfnC
  obtain ⟨v, -, hp_tendsto⟩ := exists_tendsto_of_antitone_isClosed_convex_norm_sub_le
    hK_anti hK_closed hK_conv hp_mem hp_min hp_bdd
  have hw_ex (n : ℕ) :
      ∃ w ∈ convexHull ℝ (f '' Ici n), dist (p n) w < 1 / ((n : ℝ) + 1) :=
    Metric.mem_closure_iff.1 (hp_mem n) _ (by positivity)
  choose w hw_mem hw_dist using hw_ex
  refine ⟨v, w, hw_mem, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound (n : ℕ) : dist (w n) v ≤ 1 / ((n : ℝ) + 1) + dist (p n) v :=
    (dist_triangle (w n) (p n) v).trans <|
      add_le_add ((dist_comm (w n) (p n)).trans_le (hw_dist n).le) le_rfl
  refine squeeze_zero (fun _ ↦ dist_nonneg) hbound ?_
  simpa using tendsto_one_div_add_atTop_nhds_zero_nat.add
    (tendsto_iff_dist_tendsto_zero.1 hp_tendsto)

end Complete

end InnerProduct

end TauCeti
