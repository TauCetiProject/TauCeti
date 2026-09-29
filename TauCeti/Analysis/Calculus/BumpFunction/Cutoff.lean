/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Opens
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth cutoffs for compact subsets

This module provides smooth, compactly supported cutoffs for compact subsets of a
finite-dimensional real normed space. The cutoff is equal to one on a neighborhood of the compact
set and has topological support in a prescribed open set, which is the localization step used for
compact exhaustions in domain arguments.

It also provides radial cutoffs between two concentric closed balls of radii `r < R` whose
gradient is at most `c / (R - r)` for a universal constant `c`, the quantitative form needed by
iteration arguments over families of balls with shrinking gaps.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.
-/

public section

open Function Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- A compact set contained in an open set admits a smooth cutoff equal to one on a neighborhood
of the compact set.

The cutoff takes values in `[0, 1]`, has compact support, and its topological support is contained
in the prescribed open set. -/
theorem _root_.IsCompact.exists_contDiff_cutoff [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
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

/-- A compact set contained in an open set admits a smooth cutoff whose value and gradient are
bounded by a common nonnegative constant. -/
theorem _root_.IsCompact.exists_contDiff_cutoff_with_bounds [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ψ : E → ℝ, ∃ M : ℝ,
      ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        K ⊆ interior (ψ ⁻¹' {1}) ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
          0 ≤ M ∧ (∀ x, |ψ x| ≤ M) ∧ ∀ x, ‖∇ ψ x‖ ≤ M := by
  obtain ⟨ψ, hψ, hψ_range, hψ_one_nhds, hψ_cpt, hψ_ts⟩ :=
    hK.exists_contDiff_cutoff hU hKU
  have hψ_mem : ∀ x, ψ x ∈ Icc (0 : ℝ) 1 := fun x => hψ_range (mem_range_self x)
  obtain ⟨C, hC⟩ := (hψ.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    ((hψ_cpt.fderiv ℝ).norm)
  let M : ℝ := max 1 C
  have hM0 : (0 : ℝ) ≤ M := zero_le_one.trans (le_max_left _ _)
  have hψM : ∀ x, |ψ x| ≤ M := fun x => by
    rw [abs_of_nonneg (hψ_mem x).1]
    exact (hψ_mem x).2.trans (le_max_left _ _)
  have hgradψM : ∀ x, ‖∇ ψ x‖ ≤ M := fun x => by
    rw [_root_.gradient, LinearIsometryEquiv.norm_map]
    exact (hC ⟨x, rfl⟩).trans (le_max_right _ _)
  exact ⟨ψ, M, hψ, hψ_range, hψ_one_nhds, hψ_cpt, hψ_ts, hM0, hψM, hgradψM⟩

/-- A compactly supported `C¹` function and its gradient are bounded by a common nonnegative
constant. -/
theorem _root_.ContDiff.exists_abs_le_and_norm_gradient_le [InnerProductSpace ℝ E]
    [CompleteSpace E] {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcpt : HasCompactSupport ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x, |ψ x| ≤ M) ∧ ∀ x, ‖∇ ψ x‖ ≤ M := by
  obtain ⟨C, hC⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hcpt.norm
  obtain ⟨D, hD⟩ := (hψ.continuous_fderiv one_ne_zero).norm.bddAbove_range_of_hasCompactSupport
    (hcpt.fderiv ℝ).norm
  refine ⟨max 0 (max C D), le_max_left _ _, fun x => ?_, fun x => ?_⟩
  · rw [← Real.norm_eq_abs]
    exact (hC ⟨x, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [_root_.gradient, LinearIsometryEquiv.norm_map]
    exact (hD ⟨x, rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- A compact-exhaustion term in an open set admits a smooth cutoff supported in the interior of
the next term. -/
theorem _root_.CompactExhaustion.exists_contDiff_cutoff [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Omega : Opens E} (K : CompactExhaustion Omega) (n : ℕ) :
    ∃ ψ : E → ℝ,
      ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
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
  exact ⟨ψ, hψ_smooth, hψ_range, hψ_eq_one_nhds, hψ_compact, hψ_tsupp⟩

/-- **Radial cutoffs with a quantitative gradient bound.** There is a universal constant `c` such
that for every centre `x₀` and radii `0 < r < R`, some smooth `ψ` with values in `[0, 1]` equals
one on `closedBall x₀ r`, has topological support in `closedBall x₀ R`, and satisfies

`‖∇ψ x‖ ≤ c / (R - r)` for every `x`.

The inverse dependence on the gap `R - r` is what iteration arguments over families of balls with
geometrically shrinking gaps need. The cutoff is `Real.smoothTransition ((R - ‖x - x₀‖) / (R - r))`,
and `c` is a Lipschitz constant of `Real.smoothTransition`. -/
theorem exists_forall_contDiff_cutoff_closedBall [InnerProductSpace ℝ E] [CompleteSpace E] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x₀ : E) {r R : ℝ}, 0 < r → r < R →
      ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧ EqOn ψ 1 (Metric.closedBall x₀ r) ∧
        tsupport ψ ⊆ Metric.closedBall x₀ R ∧ ∀ x, ‖∇ ψ x‖ ≤ c / (R - r) := by
  -- `Real.smoothTransition` factors through the projection onto `[0, 1]`, where it is Lipschitz.
  obtain ⟨L, hL⟩ : ∃ L, LipschitzWith L Real.smoothTransition := by
    obtain ⟨L, hL⟩ := (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
      one_ne_zero (convex_Icc (0 : ℝ) 1) isCompact_Icc
    refine ⟨L, ?_⟩
    have := hL.to_restrict.comp (LipschitzWith.projIcc (zero_le_one' ℝ))
    simpa [Function.comp_def] using this
  refine ⟨L, L.2, fun x₀ r R hr hrR => ?_⟩
  have hRr : 0 < R - r := sub_pos.2 hrR
  set ψ : E → ℝ := fun x => Real.smoothTransition ((R - ‖x - x₀‖) / (R - r))
  have hone : ∀ x, ‖x - x₀‖ ≤ r → ψ x = 1 := fun x hx =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hRr]; linarith)
  refine ⟨ψ, ?_, ?_, fun x hx => hone x (by rwa [Metric.mem_closedBall, dist_eq_norm] at hx),
    ?_, fun x => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = x₀
    · -- Near the centre, `ψ` is identically one.
      subst hx
      have hev : ψ =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Metric.ball_mem_nhds x hr] with y hy
        exact hone y (by rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le)
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y - x₀‖) x :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)
      exact Real.smoothTransition.contDiffAt.comp x ((contDiffAt_const.sub hn).div_const _)
  · rintro _ ⟨x, rfl⟩
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra h
    exact hx (Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hRr.le))
  · have hlip : LipschitzWith (L * Real.toNNReal (R - r)⁻¹) ψ := by
      refine hL.comp (LipschitzWith.of_dist_le_mul fun y z => ?_)
      rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hRr.le), ← sub_div, abs_div,
        abs_of_pos hRr, div_eq_inv_mul]
      gcongr
      rw [dist_eq_norm, show R - ‖y - x₀‖ - (R - ‖z - x₀‖) = ‖z - x₀‖ - ‖y - x₀‖ by ring,
        abs_sub_comm]
      simpa using abs_norm_sub_norm_le (y - x₀) (z - x₀)
    rw [_root_.gradient, LinearIsometryEquiv.norm_map]
    refine (norm_fderiv_le_of_lipschitz ℝ hlip).trans_eq ?_
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.2 hRr.le), div_eq_mul_inv]

end TauCeti
