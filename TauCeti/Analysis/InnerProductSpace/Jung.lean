/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Filter.Extr
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Order.Lattice
import TauCeti.Analysis.InnerProductSpace.CompleteSquare
import TauCeti.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Jung's theorem

A finite set of diameter at most `δ` in a real inner product space lies in a closed ball of radius
`δ √(d / (2 (d + 1)))`, where `d` is the dimension of its affine span, and so in a closed ball of
radius `δ / √2` in every real inner product space. The centre is the centre of the smallest
enclosing ball, which lies in the convex hull of the set.

The proof follows the route of Edelsbrunner–Harer (*Computational Topology*, p. 72). The centre `c`
of the smallest enclosing ball, of radius `R`, lies in the convex hull of the points at distance `R`
from `c`; otherwise moving `c` towards that hull would shrink every distance. By Carathéodory, `c`
is a convex combination with positive weights `w i` of affinely independent such points `z i`, at
most `d + 1` of them. The weighted variance decomposition gives
`∑ i, w i ‖z j - z i‖² = 2 R²` for each `j`, while the left side is at most `(1 - w j) δ²`;
summing over `j` gives `2 k R² ≤ (k - 1) δ²` for the number `k ≤ d + 1` of points.

## Main results

* `TauCeti.exists_isMinOn_finset_sup'_dist`: the largest distance to a nonempty finite set has a
  global minimizer, the centre of the smallest enclosing ball.
* `TauCeti.mem_convexHull_farthest_of_isMinOn`: that centre lies in the convex hull of the
  farthest points of the set.
* `TauCeti.exists_mem_convexHull_dist_le_mul_sqrt`: **Jung's theorem**, with the dimension of the
  affine span of the set.
* `TauCeti.exists_mem_convexHull_dist_le_mul_sqrt_finrank`: Jung's theorem in a
  finite-dimensional space, with the dimension of the space.
* `TauCeti.exists_mem_convexHull_dist_le_div_sqrt_two`: the dimension-free bound `δ / √2`.

## Attribution

Adapted from lean-CKSD, `CKSD/Geometry/Persistence/CechRips.lean`
(`CKSD.mem_convexHull_farthest_of_isMin`, `CKSD.exists_dist_le_sqrt_two_mul_of_dist_le`), by the
author, with AI assistance (Claude). Restated here for any real inner product space, with the
separation step done by the projection onto a compact convex set and the dimension-dependent
Jung bound added.
-/

public section

open Filter Finset Module Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The largest distance `c ↦ max_{x ∈ S} d(x, c)` to a nonempty finite set `S` has a global
minimizer: the centre of the smallest closed ball containing `S`. -/
theorem exists_isMinOn_finset_sup'_dist {S : Finset E} (hS : S.Nonempty) :
    ∃ c, IsMinOn (fun c ↦ S.sup' hS (dist · c)) univ c := by
  have hK : IsCompact (convexHull ℝ (S : Set E)) := S.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hcont : Continuous fun c ↦ S.sup' hS (dist · c) :=
    Continuous.finset_sup'_apply hS fun x _ ↦ continuous_const.dist continuous_id
  obtain ⟨c, -, hc⟩ := hK.exists_isMinOn (hS.to_set.mono (subset_convexHull ℝ _))
    hcont.continuousOn
  refine ⟨c, fun c' _ ↦ ?_⟩
  obtain ⟨p, hp, hpc⟩ := exists_mem_forall_dist_le_of_isComplete_convex
    (hS.to_set.mono (subset_convexHull ℝ _)) hK.isComplete (convex_convexHull ℝ _) c'
  exact (hc hp).trans <| Finset.sup'_le hS _ fun x hx ↦
    (hpc x (subset_convexHull ℝ _ hx)).trans (Finset.le_sup' (dist · c') hx)

/-- A global minimizer `c` of the largest distance `c ↦ max_{x ∈ S} d(x, c)` to a nonempty finite
set `S` lies in the convex hull of the points of `S` farthest from `c`. -/
theorem mem_convexHull_farthest_of_isMinOn {S : Finset E} (hS : S.Nonempty) {c : E}
    (hc : IsMinOn (fun c ↦ S.sup' hS (dist · c)) univ c) :
    c ∈ convexHull ℝ (↑{x ∈ S | dist x c = S.sup' hS (dist · c)} : Set E) := by
  set R := S.sup' hS (dist · c)
  set K := convexHull ℝ (↑{x ∈ S | dist x c = R} : Set E)
  by_contra hcK
  obtain ⟨j, hjS, hj⟩ := S.exists_mem_eq_sup' hS (dist · c)
  have hKne : K.Nonempty := ⟨j, subset_convexHull ℝ _ (Finset.mem_filter.2 ⟨hjS, hj.symm⟩)⟩
  obtain ⟨p, hpK, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne
    ((Finset.finite_toSet _).isCompact_convexHull (𝕜 := ℝ)).isComplete (convex_convexHull ℝ _) c
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ _) hpK).1 hmin
  -- Moving `c` towards `p` brings it strictly closer to every farthest point.
  have hw : 0 < ‖p - c‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h ↦ hcK (h ▸ hpK))
  have hR : 0 ≤ R := dist_nonneg.trans (Finset.le_sup' (dist · c) hjS)
  have hev : ∀ x ∈ S, ∀ᶠ t in 𝓝[>] (0 : ℝ), dist x (c + t • (p - c)) < R := by
    intro x hx
    by_cases hxR : dist x c = R
    · have hpx : ⟪p - c, c - x⟫ ≤ -‖p - c‖ ^ 2 := by
        have hx' := hinner x (subset_convexHull ℝ _ (Finset.mem_filter.2 ⟨hx, hxR⟩))
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_comm] at hx' ⊢
        linarith
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      rw [dist_comm, ← sq_lt_sq₀ dist_nonneg hR, dist_eq_norm, norm_add_smul_sub_sq,
        ← dist_eq_norm, dist_comm, hxR]
      nlinarith [ht.1, ht.2, mul_pos ht.1 (pow_pos hw 2)]
    · have hlt : dist x c < R := (Finset.le_sup' (dist · c) hx).lt_of_ne hxR
      have hlim : Tendsto (fun t : ℝ ↦ dist x (c + t • (p - c))) (𝓝[>] 0) (𝓝 (dist x c)) := by
        have : Continuous fun t : ℝ ↦ dist x (c + t • (p - c)) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      exact hlim.eventually (gt_mem_nhds hlt)
  obtain ⟨t, ht⟩ := ((Filter.eventually_all_finset S).2 hev).exists
  exact (hc (mem_univ (c + t • (p - c)))).not_gt ((Finset.sup'_lt_iff hS).2 ht)

/-- **Jung's theorem.** A nonempty finite set `S` of diameter at most `δ` in a real inner product
space lies in the closed ball of radius `δ √(d / (2 (d + 1)))` about a point of its convex hull,
where `d` is the dimension of the affine span of `S`. -/
theorem exists_mem_convexHull_dist_le_mul_sqrt {S : Finset E} (hS : S.Nonempty) {δ : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ) :
    ∃ c ∈ convexHull ℝ (S : Set E), ∀ x ∈ S, dist x c ≤
      δ * √(finrank ℝ (vectorSpan ℝ (S : Set E)) /
        (2 * (finrank ℝ (vectorSpan ℝ (S : Set E)) + 1))) := by
  classical
  obtain ⟨c, hc⟩ := exists_isMinOn_finset_sup'_dist hS
  set R := S.sup' hS (dist · c)
  have hcF := mem_convexHull_farthest_of_isMinOn hS hc
  obtain ⟨ι, _, z, w, hzF, hz, hw0, hw1, hwc⟩ := eq_pos_convex_span_of_mem_convexHull hcF
  have hzS (i : ι) : z i ∈ S ∧ dist (z i) c = R := Finset.mem_filter.1 (hzF ⟨i, rfl⟩)
  -- At most `d + 1` affinely independent points of `S`.
  have : FiniteDimensional ℝ (vectorSpan ℝ (S : Set E)) :=
    finiteDimensional_vectorSpan_of_finite ℝ S.finite_toSet
  have hk : Fintype.card ι ≤ finrank ℝ (vectorSpan ℝ (S : Set E)) + 1 :=
    hz.card_le_finrank_succ.trans <| Nat.add_le_add_right (Submodule.finrank_mono
      (vectorSpan_mono ℝ (Set.range_subset_iff.2 fun i ↦ (hzS i).1))) 1
  have hk1 : 0 < Fintype.card ι := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp at hw1
    · exact Fintype.card_pos
  -- The weighted mean squared distance from each `z j` is `2 R²` and at most `(1 - w j) δ²`.
  have hid (j : ι) : ∑ i, w i * ‖z j - z i‖ ^ 2 = 2 * R ^ 2 := by
    rw [Finset.sum_mul_norm_sub_sq_eq _ hw1, hwc]
    simp only [← dist_eq_norm, dist_comm c, (hzS _).2, ← Finset.sum_mul, hw1]
    ring
  have hle (j : ι) : 2 * R ^ 2 ≤ (1 - w j) * δ ^ 2 := by
    rw [← hid, ← Finset.add_sum_erase _ _ (mem_univ j), sub_self, norm_zero, ← hw1,
      ← Finset.add_sum_erase _ _ (mem_univ j), add_sub_cancel_left, Finset.sum_mul]
    refine (zero_add _).trans_le (Finset.sum_le_sum fun i _ ↦ ?_) |>.trans_eq' (by ring)
    rw [← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ dist_nonneg (h _ (hzS j).1 _ (hzS i).1) 2) (hw0 i).le
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset ι)) ↦ hle j
  simp only [sum_const, card_univ, nsmul_eq_mul, ← Finset.sum_mul, sum_sub_distrib, hw1] at hsum
  obtain ⟨x₀, hx₀⟩ := hS
  have hδ : 0 ≤ δ := (dist_self x₀).symm.trans_le (h x₀ hx₀ x₀ hx₀)
  refine ⟨c, convexHull_mono (Finset.coe_subset.2 (Finset.filter_subset _ _)) hcF,
    fun x hx ↦ (Finset.le_sup' (dist · c) hx).trans ?_⟩
  rw [← Real.sqrt_sq hδ, ← Real.sqrt_mul (sq_nonneg δ)]
  refine Real.le_sqrt_of_sq_le ?_
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  have hk' : (Fintype.card ι : ℝ) ≤ finrank ℝ (vectorSpan ℝ (S : Set E)) + 1 := by
    exact_mod_cast hk
  have hk1' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hk1
  nlinarith [mul_le_mul_of_nonneg_right hk' (sq_nonneg δ), sq_nonneg R]

/-- **Jung's theorem** in a finite-dimensional real inner product space of dimension `d`: a
nonempty finite set of diameter at most `δ` lies in the closed ball of radius
`δ √(d / (2 (d + 1)))` about a point of its convex hull. -/
theorem exists_mem_convexHull_dist_le_mul_sqrt_finrank [FiniteDimensional ℝ E] {S : Finset E}
    (hS : S.Nonempty) {δ : ℝ} (h : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ) :
    ∃ c ∈ convexHull ℝ (S : Set E), ∀ x ∈ S,
      dist x c ≤ δ * √(finrank ℝ E / (2 * (finrank ℝ E + 1))) := by
  obtain ⟨c, hc, hcS⟩ := exists_mem_convexHull_dist_le_mul_sqrt hS h
  obtain ⟨x₀, hx₀⟩ := hS
  have hδ : 0 ≤ δ := (dist_self x₀).symm.trans_le (h x₀ hx₀ x₀ hx₀)
  have hd : (finrank ℝ (vectorSpan ℝ (S : Set E)) : ℝ) ≤ finrank ℝ E := by
    exact_mod_cast Submodule.finrank_le _
  refine ⟨c, hc, fun x hx ↦ (hcS x hx).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt ?_) hδ)⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- A nonempty finite set of diameter at most `δ` in a real inner product space lies in the closed
ball of radius `δ / √2` about a point of its convex hull. This is the dimension-free form of
Jung's theorem. -/
theorem exists_mem_convexHull_dist_le_div_sqrt_two {S : Finset E} (hS : S.Nonempty) {δ : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ δ) :
    ∃ c ∈ convexHull ℝ (S : Set E), ∀ x ∈ S, dist x c ≤ δ / √2 := by
  obtain ⟨c, hc, hcS⟩ := exists_mem_convexHull_dist_le_mul_sqrt hS h
  obtain ⟨x₀, hx₀⟩ := hS
  have hδ : 0 ≤ δ := (dist_self x₀).symm.trans_le (h x₀ hx₀ x₀ hx₀)
  refine ⟨c, hc, fun x hx ↦ (hcS x hx).trans ?_⟩
  rw [div_eq_mul_inv δ, ← Real.sqrt_inv]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hδ
  rw [div_le_iff₀ (by positivity)]
  linarith

end TauCeti
