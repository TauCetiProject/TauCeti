/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import TauCeti.Analysis.Normed.Group.Cover

/-!
# Operator norms and sphere nets

Finite nets on the unit spheres of real normed spaces reduce an operator norm into a real inner
product space to finitely many bilinear evaluations. For two nets of radius `η < 1 / 2`, the loss
is the factor `(1 - 2η)⁻¹`, which is `2` when `η = 1 / 4`.

## Main results

* `ContinuousLinearMap.abs_real_inner_sub_le`: perturbation estimate for the bilinear form
  `(v, x) ↦ ⟪v, T x⟫` on pairs of nearby points.
* `ContinuousLinearMap.opNorm_le_of_isCover_sphere`: the bilinear `η`-net bound for the operator
  norm.
-/

public section

open Metric

namespace ContinuousLinearMap

/-- Perturbation estimate for the bilinear form `(v, x) ↦ ⟪v, T x⟫`: if `‖x‖ ≤ 1`, `‖v‖ ≤ 1`,
`‖x - u‖ ≤ η` and `‖y - v‖ ≤ η`, then `⟪y, T x⟫` and `⟪v, T u⟫` differ by at most `2 η ‖T‖`. -/
theorem abs_real_inner_sub_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : E →L[ℝ] F) {η : ℝ} {x u : E}
    {y v : F} (hx : ‖x‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hxu : ‖x - u‖ ≤ η) (hyv : ‖y - v‖ ≤ η) :
    |Inner.inner ℝ y (T x) - Inner.inner ℝ v (T u)| ≤ 2 * η * ‖T‖ := by
  have hdecomp :
      Inner.inner ℝ y (T x) - Inner.inner ℝ v (T u) =
        Inner.inner ℝ (y - v) (T x) + Inner.inner ℝ v (T (x - u)) := by
    simp only [inner_sub_left, inner_sub_right, map_sub]
    ring
  have hTxle : ‖T x‖ ≤ ‖T‖ :=
    (T.le_opNorm x).trans (mul_le_of_le_one_right T.opNorm_nonneg hx)
  have hTdiff : ‖T (x - u)‖ ≤ ‖T‖ * η :=
    (T.le_opNorm (x - u)).trans (mul_le_mul_of_nonneg_left hxu T.opNorm_nonneg)
  rw [hdecomp]
  calc
    |Inner.inner ℝ (y - v) (T x) + Inner.inner ℝ v (T (x - u))|
        ≤ |Inner.inner ℝ (y - v) (T x)| + |Inner.inner ℝ v (T (x - u))| := abs_add_le _ _
    _ ≤ ‖y - v‖ * ‖T x‖ + ‖v‖ * ‖T (x - u)‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ η * ‖T‖ + 1 * (‖T‖ * η) :=
      add_le_add (mul_le_mul hyv hTxle (norm_nonneg _) (hxu.trans' (norm_nonneg _)))
        (mul_le_mul hv hTdiff (norm_nonneg _) zero_le_one)
    _ = 2 * η * ‖T‖ := by ring

/-- A bilinear `η`-net bound for the operator norm. If `Nₙ` and `Nₚ` cover the unit spheres in
the domain and codomain with radius `η < 1 / 2`, the points of `Nₚ` lie in the closed unit ball,
and `M ≥ 0` bounds `|⟪v, T u⟫|` over `u ∈ Nₙ` and `v ∈ Nₚ`, then `‖T‖ ≤ (1 - 2η)⁻¹ * M`.
In particular, `η = 1 / 4` gives the factor `2`. -/
theorem opNorm_le_of_isCover_sphere {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : E →L[ℝ] F)
    {η : NNReal} (hη : η < (1 / 2 : NNReal)) {Nₙ : Set E} {Nₚ : Set F} {M : ℝ} (hM0 : 0 ≤ M)
    (hNₚ : Nₚ ⊆ closedBall (0 : F) 1)
    (hM : ∀ u ∈ Nₙ, ∀ v ∈ Nₚ, |Inner.inner ℝ v (T u)| ≤ M)
    (hcoverₙ : IsCover η (sphere (0 : E) 1) Nₙ) (hcoverₚ : IsCover η (sphere (0 : F) 1) Nₚ) :
    ‖T‖ ≤ (1 - 2 * (η : ℝ))⁻¹ * M := by
  have hηreal : (η : ℝ) < 1 / 2 := by exact_mod_cast hη
  have hden : 0 < 1 - 2 * (η : ℝ) := by nlinarith
  have hunit : ∀ x : E, ‖x‖ = 1 → ‖T x‖ ≤ M + 2 * (η : ℝ) * ‖T‖ := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := hcoverₙ.exists_norm_sub_le (mem_sphere_zero_iff_norm.mpr hx)
    by_cases hTx : T x = 0
    · rw [hTx]
      have : 0 ≤ M + 2 * (η : ℝ) * ‖T‖ := by positivity
      simpa using this
    · let y : F := ‖T x‖⁻¹ • T x
      have hynorm : ‖y‖ = 1 := by
        simpa only [y, RCLike.ofReal_real_eq_id, id_eq] using
          norm_smul_inv_norm (𝕜 := ℝ) hTx
      have hinner : Inner.inner ℝ y (T x) = ‖T x‖ := by
        dsimp only [y]
        rw [real_inner_smul_self_left]
        field_simp [norm_ne_zero_iff.mpr hTx]
      obtain ⟨v, hv, hyv⟩ := hcoverₚ.exists_norm_sub_le (mem_sphere_zero_iff_norm.mpr hynorm)
      have herror := T.abs_real_inner_sub_le hx.le (mem_closedBall_zero_iff.mp (hNₚ hv)) hxu hyv
      have htri := abs_sub_abs_le_abs_sub (Inner.inner ℝ y (T x)) (Inner.inner ℝ v (T u))
      have hsample := hM u hu v hv
      have habs : |Inner.inner ℝ y (T x)| = ‖T x‖ := by
        rw [hinner, abs_of_nonneg (norm_nonneg _)]
      linarith
  have hnorm : ‖T‖ ≤ M + 2 * (η : ℝ) * ‖T‖ :=
    ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) hunit
  have hsolve : (1 - 2 * (η : ℝ)) * ‖T‖ ≤ M := by
    nlinarith [hnorm]
  calc
    ‖T‖ = (1 - 2 * (η : ℝ))⁻¹ * ((1 - 2 * (η : ℝ)) * ‖T‖) := by
      field_simp
    _ ≤ (1 - 2 * (η : ℝ))⁻¹ * M :=
      mul_le_mul_of_nonneg_left hsolve (inv_nonneg.mpr hden.le)

end ContinuousLinearMap
