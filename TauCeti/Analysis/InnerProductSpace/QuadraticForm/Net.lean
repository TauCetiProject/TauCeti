/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Quadratic-form bounds from sphere nets

A bound for the quadratic form of a symmetric operator on an `η`-net of the unit sphere controls
its operator norm, with loss `(1 - 2η)⁻¹`.

## References

* R. Vershynin, *High-Dimensional Probability*, 2018, Lemma 4.4.1 and Exercise 4.4.3.
* T. Tao, *Topics in Random Matrix Theory*, §2.3.
-/

public section

open Metric RCLike

namespace ContinuousLinearMap

/-- The quadratic form of a continuous linear map changes by at most `2η ‖T‖` between vectors
in the closed unit ball that are within `η` of each other. -/
theorem norm_inner_map_self_sub_le {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) {η : ℝ} {x y : E}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hxy : ‖x - y‖ ≤ η) :
    ‖Inner.inner 𝕜 (T x) x - Inner.inner 𝕜 (T y) y‖ ≤ 2 * η * ‖T‖ := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hxy
  have hdecomp :
      Inner.inner 𝕜 (T x) x - Inner.inner 𝕜 (T y) y =
        Inner.inner 𝕜 (T (x - y)) x + Inner.inner 𝕜 (T y) (x - y) := by
    rw [map_sub]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hTy : ‖T y‖ ≤ ‖T‖ := by
    simpa using T.le_opNorm_of_le hy
  have hTxy : ‖T (x - y)‖ ≤ ‖T‖ * η := T.le_opNorm_of_le hxy
  rw [hdecomp]
  calc
    ‖Inner.inner 𝕜 (T (x - y)) x + Inner.inner 𝕜 (T y) (x - y)‖
        ≤ ‖Inner.inner 𝕜 (T (x - y)) x‖ + ‖Inner.inner 𝕜 (T y) (x - y)‖ :=
          norm_add_le _ _
    _ ≤ ‖T (x - y)‖ * ‖x‖ + ‖T y‖ * ‖x - y‖ :=
          add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ (‖T‖ * η) * 1 + ‖T‖ * η := by
      gcongr
    _ = 2 * η * ‖T‖ := by ring

/-- For a symmetric continuous linear map, a uniform bound on the real part of its quadratic
form over unit vectors bounds its operator norm. -/
theorem norm_le_of_forall_norm_eq_one_abs_re_inner_map_self_le {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) (hT : T.IsSymmetric)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : E, ‖x‖ = 1 → |RCLike.re (Inner.inner 𝕜 (T x) x)| ≤ C) : ‖T‖ ≤ C := by
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  refine ciSup_le fun x ↦ ?_
  by_cases hx : x = 0
  · subst x
    simpa only [rayleighQuotient_apply_zero, abs_zero] using hC
  · have hxmem : T.rayleighQuotient x ∈
        T.rayleighQuotient '' ({0}ᶜ : Set E) := ⟨x, hx, rfl⟩
    rw [T.image_rayleigh_eq_image_rayleigh_sphere (by norm_num : (0 : ℝ) < 1)] at hxmem
    obtain ⟨y, hy, hxy⟩ := hxmem
    have hy_norm : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
    have hquotient : T.rayleighQuotient y =
        RCLike.re (Inner.inner 𝕜 (T y) y) := by
      simp [rayleighQuotient, reApplyInnerSelf_apply, hy_norm]
    rw [← hxy, hquotient]
    exact h y hy_norm

/-- A bound on the real part of a symmetric operator's quadratic form on an `η`-cover of the
unit sphere bounds its operator norm. The cover points may lie anywhere in the closed unit ball.
-/
theorem norm_le_of_isSymmetric_of_abs_re_inner_map_self_le_of_isCover
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (T : E →L[𝕜] E) (hT : T.IsSymmetric) {η : NNReal} (hη : η < (1 / 2 : NNReal))
    {N : Set E} {M : ℝ} (hM0 : 0 ≤ M) (hN : N ⊆ closedBall (0 : E) 1)
    (hM : ∀ x ∈ N, |RCLike.re (Inner.inner 𝕜 (T x) x)| ≤ M)
    (hcover : IsCover η (sphere (0 : E) 1) N) :
    ‖T‖ ≤ (1 - 2 * (η : ℝ))⁻¹ * M := by
  have hηreal : (η : ℝ) < 1 / 2 := by exact_mod_cast hη
  have hden : 0 < 1 - 2 * (η : ℝ) := by nlinarith
  -- Transfer the net bound to every unit vector, with the quadratic-form error controlled by
  -- the distance to its net point.
  have hunit : ∀ x : E, ‖x‖ = 1 →
      |RCLike.re (Inner.inner 𝕜 (T x) x)| ≤ M + 2 * (η : ℝ) * ‖T‖ := by
    intro x hx
    obtain ⟨z, hzN, hdist⟩ :
        ∃ z : E, z ∈ N ∧ x ∈ closedBall z η := by
      simpa only [Set.mem_iUnion, exists_prop] using
        (IsCover.subset_iUnion_closedBall hcover) (mem_sphere_zero_iff_norm.mpr hx)
    have hznorm : ‖z‖ ≤ 1 := by
      simpa [mem_closedBall, dist_eq_norm] using hN hzN
    have hdist' : ‖x - z‖ ≤ (η : ℝ) := by
      simpa [mem_closedBall, dist_eq_norm] using hdist
    have herror := norm_inner_map_self_sub_le T hx.le hznorm hdist'
    have herror' :
        |RCLike.re (Inner.inner 𝕜 (T x) x) - RCLike.re (Inner.inner 𝕜 (T z) z)| ≤
          2 * (η : ℝ) * ‖T‖ := by
      rw [← map_sub]
      exact (abs_re_le_norm _).trans herror
    calc
      |RCLike.re (Inner.inner 𝕜 (T x) x)| =
          |(RCLike.re (Inner.inner 𝕜 (T x) x) - RCLike.re (Inner.inner 𝕜 (T z) z)) +
            RCLike.re (Inner.inner 𝕜 (T z) z)| := by rw [sub_add_cancel]
      _ ≤ |RCLike.re (Inner.inner 𝕜 (T x) x) - RCLike.re (Inner.inner 𝕜 (T z) z)| +
          |RCLike.re (Inner.inner 𝕜 (T z) z)| := abs_add_le _ _
      _ ≤ 2 * (η : ℝ) * ‖T‖ + M := add_le_add herror' (hM z hzN)
      _ = M + 2 * (η : ℝ) * ‖T‖ := by ring
  -- The Rayleigh-quotient characterization turns the unit-vector estimate into an operator-norm
  -- bound; rearrange to absorb the error term, using η < 1/2.
  have hnorm : ‖T‖ ≤ M + 2 * (η : ℝ) * ‖T‖ :=
    norm_le_of_forall_norm_eq_one_abs_re_inner_map_self_le T hT
      (add_nonneg hM0 (mul_nonneg (by positivity) (norm_nonneg T))) hunit
  have hsolve : (1 - 2 * (η : ℝ)) * ‖T‖ ≤ M := by nlinarith
  exact (le_inv_mul_iff₀ hden).mpr hsolve

end ContinuousLinearMap
