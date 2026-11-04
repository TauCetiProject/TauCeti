/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Quadratic forms and sphere nets

A bound for the quadratic form of a symmetric operator on an `η`-net of the unit sphere controls
its operator norm, with loss `(1 - 2η)⁻¹`.
-/

public section

open Metric

namespace ContinuousLinearMap

private theorem abs_inner_self_sub_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E) {η : ℝ} {x y : E}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hxy : ‖x - y‖ ≤ η) :
    |Inner.inner ℝ (T x) x - Inner.inner ℝ (T y) y| ≤ 2 * η * ‖T‖ := by
  have hdecomp :
      Inner.inner ℝ (T x) x - Inner.inner ℝ (T y) y =
        Inner.inner ℝ (T (x - y)) x + Inner.inner ℝ (T y) (x - y) := by
    rw [map_sub]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hTx : ‖T x‖ ≤ ‖T‖ :=
    (T.le_opNorm x).trans (mul_le_of_le_one_right T.opNorm_nonneg hx)
  have hTy : ‖T y‖ ≤ ‖T‖ :=
    (T.le_opNorm y).trans (mul_le_of_le_one_right T.opNorm_nonneg hy)
  have hTxy : ‖T (x - y)‖ ≤ ‖T‖ * η :=
    (T.le_opNorm (x - y)).trans (mul_le_mul_of_nonneg_left hxy T.opNorm_nonneg)
  rw [hdecomp]
  calc
    |Inner.inner ℝ (T (x - y)) x + Inner.inner ℝ (T y) (x - y)|
        ≤ |Inner.inner ℝ (T (x - y)) x| + |Inner.inner ℝ (T y) (x - y)| :=
          abs_add_le _ _
    _ ≤ ‖T (x - y)‖ * ‖x‖ + ‖T y‖ * ‖x - y‖ :=
          add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (‖T‖ * η) * 1 + ‖T‖ * η :=
          add_le_add
            (mul_le_mul hTxy hx (norm_nonneg _)
              (mul_nonneg T.opNorm_nonneg (le_trans (norm_nonneg _) hxy)))
            (mul_le_mul hTy hxy (norm_nonneg _) T.opNorm_nonneg)
    _ = 2 * η * ‖T‖ := by ring

/-- A bound on the quadratic form of a symmetric operator on an `η`-cover of the unit sphere
bounds its operator norm. The cover points must themselves lie on the sphere. -/
theorem norm_le_of_isCover_sphere_quadratic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E) (hT : T.IsSymmetric)
    {η : NNReal} (hη : η < (1 / 2 : NNReal)) {N : Set E} {M : ℝ} (hM0 : 0 ≤ M)
    (hN : N ⊆ sphere (0 : E) 1)
    (hM : ∀ x ∈ N, |Inner.inner ℝ (T x) x| ≤ M)
    (hcover : IsCover η (sphere (0 : E) 1) N) :
    ‖T‖ ≤ (1 - 2 * (η : ℝ))⁻¹ * M := by
  have hη0 : 0 ≤ (η : ℝ) := η.coe_nonneg
  have hηreal : (η : ℝ) < 1 / 2 := by exact_mod_cast hη
  have hden : 0 < 1 - 2 * (η : ℝ) := by nlinarith
  have hunit : ∀ x : E, ‖x‖ = 1 →
      |T.rayleighQuotient x| ≤ M + 2 * (η : ℝ) * ‖T‖ := by
    intro x hx
    obtain ⟨z, hzN, hdist⟩ :
        ∃ z : E, z ∈ N ∧ x ∈ closedBall z η := by
      simpa only [Set.mem_iUnion, exists_prop] using
        (IsCover.subset_iUnion_closedBall hcover) (mem_sphere_zero_iff_norm.mpr hx)
    have hznorm : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp (hN hzN)
    have hdist' : ‖x - z‖ ≤ (η : ℝ) := by
      simpa [mem_closedBall, dist_eq_norm] using hdist
    have herror := abs_inner_self_sub_le T hx.le hznorm.le hdist'
    have hqx : T.rayleighQuotient x = Inner.inner ℝ (T x) x := by
      simp [rayleighQuotient, reApplyInnerSelf_apply, hx]
    have hqz : T.rayleighQuotient z = Inner.inner ℝ (T z) z := by
      simp [rayleighQuotient, reApplyInnerSelf_apply, hznorm]
    rw [← hqx, ← hqz] at herror
    have hM' : |T.rayleighQuotient z| ≤ M := by
      simpa only [← hqz] using hM z hzN
    calc
      |T.rayleighQuotient x| =
          |(T.rayleighQuotient x - T.rayleighQuotient z) +
            T.rayleighQuotient z| := by ring_nf
      _ ≤ |T.rayleighQuotient x - T.rayleighQuotient z| +
          |T.rayleighQuotient z| := abs_add_le _ _
      _ ≤ 2 * (η : ℝ) * ‖T‖ + M :=
          add_le_add herror hM'
      _ = M + 2 * (η : ℝ) * ‖T‖ := by ring
  have hnorm : ‖T‖ ≤ M + 2 * (η : ℝ) * ‖T‖ := by
    calc
      ‖T‖ = ⨆ x, |T.rayleighQuotient x| := T.norm_eq_iSup_rayleighQuotient hT
      _ ≤ M + 2 * (η : ℝ) * ‖T‖ := ciSup_le fun x ↦ by
        by_cases hx : x = 0
        · subst x
          simpa only [rayleighQuotient_apply_zero, abs_zero] using
            (add_nonneg hM0 (mul_nonneg (by positivity) (norm_nonneg T)))
        · let y : E := ‖x‖⁻¹ • x
          have hy : ‖y‖ = 1 := by
            simpa only [y, RCLike.ofReal_real_eq_id, id_eq] using
              norm_smul_inv_norm (𝕜 := ℝ) hx
          have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
          have hscale : T.rayleighQuotient y = T.rayleighQuotient x := by
            dsimp [y]
            exact T.rayleigh_smul x (inv_ne_zero hxnorm)
          rw [← hscale]
          exact hunit y hy
  have hsolve : (1 - 2 * (η : ℝ)) * ‖T‖ ≤ M := by nlinarith
  calc
    ‖T‖ = (1 - 2 * (η : ℝ))⁻¹ * ((1 - 2 * (η : ℝ)) * ‖T‖) := by
      field_simp [hden.ne']
    _ ≤ (1 - 2 * (η : ℝ))⁻¹ * M :=
      mul_le_mul_of_nonneg_left hsolve (inv_nonneg.mpr hden.le)

end ContinuousLinearMap
