/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Linear

/-!
# Harnack's inequality and convergence theorem for affine functions

Affine functions are harmonic (`ContinuousLinearMap.harmonicOnNhd`), and they show which
hypotheses of Harnack's inequality and of Harnack's convergence theorem are needed. Let `e` be a
unit vector of a finite-dimensional real inner product space `E`.

* **No Harnack inequality up to the boundary.** The function `u x = 1 + ⟪e, x⟫` is harmonic and
  nonnegative on the closed unit ball, but it takes the value `2` at `e` and `0` at `-e`, so no
  inequality `u x ≤ C u y` holds on the closed ball
  (`TauCeti.Examples.HarnackAffine.not_exists_forall_one_add_inner_le_mul`). Harnack's
  inequality with the sharp constant
  (`InnerProductSpace.HarmonicOnNhd.le_add_div_sub_pow_mul_of_nonneg`) applies only on balls
  `closedBall 0 r` with `r < 1`. There `u` ranges over `[1 - r, 1 + r]`
  (`TauCeti.Examples.HarnackAffine.isGreatest_image_inner_closedBall`,
  `TauCeti.Examples.HarnackAffine.isLeast_image_inner_closedBall`), so its extreme values have the
  ratio `(1 + r) / (1 - r)`, which is `5 / 3` at `r = 1 / 4`. In dimension one this is the sharp
  constant `((1 + r) / (1 - r)) ^ n`, attained at `±r e`
  (`TauCeti.Examples.HarnackAffine.one_add_inner_smul_eq_mul_of_finrank_eq_one`); in higher
  dimensions the Poisson kernel attains it
  (`TauCeti.exists_harmonicOnNhd_ball_eq_add_div_sub_pow_mul`).
* **Nonnegativity is needed.** The sign-changing harmonic function `x ↦ ⟪e, x⟫` satisfies no
  inequality `⟪e, x⟫ ≤ C ⟪e, y⟫` on any closed ball of positive radius about `0`
  (`TauCeti.Examples.HarnackAffine.not_exists_forall_inner_le_mul`).
* **Both cases of the convergence theorem occur.** By Harnack's convergence theorem
  (`TauCeti.tendstoLocallyUniformlyOn_iSup_or_tendsto_atTop_of_monotone`), a monotone sequence of
  harmonic functions on a connected open set either converges locally uniformly to a harmonic
  function or tends to `+∞` locally uniformly. The constant functions `m`, `m ∈ ℕ`, tend to `+∞`
  uniformly on every set (`TauCeti.Examples.HarnackAffine.tendsto_natCast_atTop`) and converge
  locally uniformly on no nonempty set
  (`TauCeti.Examples.HarnackAffine.not_exists_tendstoLocallyUniformlyOn_natCast`), so the
  divergent case cannot be omitted. The functions `⟪e, x⟫ - 1 / (m + 1)` increase
  (`TauCeti.Examples.HarnackAffine.monotone_inner_sub_one_div`) to their supremum `⟪e, x⟫`
  (`TauCeti.Examples.HarnackAffine.iSup_inner_sub_one_div`), uniformly on `E`
  (`TauCeti.Examples.HarnackAffine.tendstoUniformly_inner_sub_one_div`), and the limit is harmonic.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 2.5 and 2.9.
-/

public section

namespace TauCeti.Examples.HarnackAffine

open InnerProductSpace Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E} {r : ℝ}

/-- The affine function `x ↦ 1 + ⟪e, x⟫` is harmonic. -/
theorem harmonicOnNhd_one_add_inner [FiniteDimensional ℝ E] (e : E) (s : Set E) :
    HarmonicOnNhd (fun x ↦ 1 + ⟪e, x⟫_ℝ) s :=
  (harmonicOnNhd_const (1 : ℝ)).add ((innerSL ℝ e).harmonicOnNhd s)

/-- For a unit vector `e` and `r ≥ 0`, the largest value of `⟪e, ·⟫` on `closedBall 0 r` is `r`,
attained at `r e`. -/
theorem isGreatest_image_inner_closedBall (he : ‖e‖ = 1) (hr : 0 ≤ r) :
    IsGreatest ((fun x ↦ ⟪e, x⟫_ℝ) '' closedBall 0 r) r := by
  refine ⟨⟨r • e, ?_, ?_⟩, ?_⟩
  · simp [norm_smul, he, abs_of_nonneg hr]
  · simp [real_inner_smul_right, he]
  · rintro _ ⟨x, hx, rfl⟩
    have h := real_inner_le_norm e x
    rw [he, one_mul] at h
    exact h.trans (mem_closedBall_zero_iff.1 hx)

/-- For a unit vector `e` and `r ≥ 0`, the least value of `⟪e, ·⟫` on `closedBall 0 r` is `-r`,
attained at `-r e`. -/
theorem isLeast_image_inner_closedBall (he : ‖e‖ = 1) (hr : 0 ≤ r) :
    IsLeast ((fun x ↦ ⟪e, x⟫_ℝ) '' closedBall 0 r) (-r) := by
  refine ⟨⟨-(r • e), ?_, ?_⟩, ?_⟩
  · simp [norm_smul, he, abs_of_nonneg hr]
  · simp [real_inner_smul_right, he]
  · rintro _ ⟨x, hx, rfl⟩
    have h := neg_le_of_abs_le (abs_real_inner_le_norm e x)
    rw [he, one_mul] at h
    exact (neg_le_neg (mem_closedBall_zero_iff.1 hx)).trans h

/-- For a unit vector `e`, the function `1 + ⟪e, x⟫` is nonnegative on the closed unit ball. -/
theorem one_add_inner_nonneg (he : ‖e‖ = 1) {x : E} (hx : x ∈ closedBall 0 1) :
    0 ≤ 1 + ⟪e, x⟫_ℝ := by
  have h := (isLeast_image_inner_closedBall he zero_le_one).2 ⟨x, hx, rfl⟩
  linarith

/-- **No Harnack inequality up to the boundary.** For a unit vector `e`, the nonnegative harmonic
function `u x = 1 + ⟪e, x⟫` satisfies no inequality `u x ≤ C u y` on the closed unit ball: it
takes the value `2` at `e` and `0` at `-e`. -/
theorem not_exists_forall_one_add_inner_le_mul (he : ‖e‖ = 1) :
    ¬∃ C : ℝ, ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      1 + ⟪e, x⟫_ℝ ≤ C * (1 + ⟪e, y⟫_ℝ) := by
  rintro ⟨C, hC⟩
  have h := hC e (by simp [he]) (-e) (by simp [he])
  simp only [inner_neg_right, real_inner_self_eq_norm_sq, he] at h
  norm_num at h

/-- **The affine function attains the sharp Harnack constant in dimension one.** If `E` has
dimension one, `e` is a unit vector and `0 ≤ r < 1`, the harmonic function `u x = 1 + ⟪e, x⟫`,
positive on the open unit ball, has `u (r e) = ((1 + r) / (1 - r)) ^ n u (-r e)` with `n = 1`:
equality in Harnack's inequality
`InnerProductSpace.HarmonicOnNhd.le_add_div_sub_pow_mul_of_nonneg` on `closedBall 0 r`. -/
theorem one_add_inner_smul_eq_mul_of_finrank_eq_one (hE : Module.finrank ℝ E = 1)
    (he : ‖e‖ = 1) (hr1 : r < 1) :
    1 + ⟪e, r • e⟫_ℝ = ((1 + r) / (1 - r)) ^ Module.finrank ℝ E * (1 + ⟪e, -(r • e)⟫_ℝ) := by
  have hsub : 1 - r ≠ 0 := by linarith
  simp only [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he, hE]
  field_simp
  ring

/-- **Nonnegativity is needed in Harnack's inequality.** For a unit vector `e` and `r > 0`, the
sign-changing harmonic function `x ↦ ⟪e, x⟫` satisfies no inequality `⟪e, x⟫ ≤ C ⟪e, y⟫` on
`closedBall 0 r`. -/
theorem not_exists_forall_inner_le_mul (he : ‖e‖ = 1) (hr : 0 < r) :
    ¬∃ C : ℝ, ∀ x ∈ closedBall (0 : E) r, ∀ y ∈ closedBall (0 : E) r,
      ⟪e, x⟫_ℝ ≤ C * ⟪e, y⟫_ℝ := by
  rintro ⟨C, hC⟩
  have hmem : r • e ∈ closedBall (0 : E) r := by simp [norm_smul, he, abs_of_pos hr]
  have hmem' : -(r • e) ∈ closedBall (0 : E) r := by simp [norm_smul, he, abs_of_pos hr]
  have h₁ := hC _ hmem _ hmem
  have h₂ := hC _ hmem _ hmem'
  simp only [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he] at h₁ h₂
  nlinarith

/-- The constant functions `m`, `m ∈ ℕ`, tend to `+∞` uniformly on every set `K`. -/
theorem tendsto_natCast_atTop {X : Type*} (K : Set X) :
    Tendsto (fun p : ℕ × X ↦ (p.1 : ℝ)) (atTop ×ˢ 𝓟 K) atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_fst

/-- The constant functions `m`, `m ∈ ℕ`, form a monotone sequence of harmonic functions that
converges locally uniformly on no nonempty set. So a monotone sequence of harmonic functions on a
connected open set need not converge, and the divergent case of Harnack's convergence theorem
`TauCeti.tendstoLocallyUniformlyOn_iSup_or_tendsto_atTop_of_monotone` cannot be omitted. -/
theorem not_exists_tendstoLocallyUniformlyOn_natCast {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : U.Nonempty) :
    ¬∃ v : X → ℝ, TendstoLocallyUniformlyOn (fun (m : ℕ) (_ : X) ↦ (m : ℝ)) v atTop U := by
  rintro ⟨v, hv⟩
  obtain ⟨x, hx⟩ := hU
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop _ (hv.tendsto_at hx)

/-- The functions `⟪e, x⟫ - 1 / (m + 1)` increase with `m` at every point. -/
theorem monotone_inner_sub_one_div (e x : E) :
    Monotone fun m : ℕ ↦ ⟪e, x⟫_ℝ - 1 / ((m : ℝ) + 1) := fun m k hmk ↦ by
  have : (m : ℝ) + 1 ≤ k + 1 := by exact_mod_cast Nat.add_le_add_right hmk 1
  dsimp only
  gcongr

/-- The functions `⟪e, x⟫ - 1 / (m + 1)` converge to `⟪e, x⟫` uniformly on `E`. -/
theorem tendstoUniformly_inner_sub_one_div (e : E) :
    TendstoUniformly (fun (m : ℕ) (x : E) ↦ ⟪e, x⟫_ℝ - 1 / ((m : ℝ) + 1)) (fun x ↦ ⟪e, x⟫_ℝ)
      atTop := by
  refine Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_
  filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε))] with m hm
    x
  rw [Real.dist_eq, sub_sub_cancel, abs_of_pos (by positivity)]
  exact hm

/-- The supremum of the functions `⟪e, x⟫ - 1 / (m + 1)` is the harmonic function `⟪e, x⟫`. -/
theorem iSup_inner_sub_one_div (e x : E) :
    ⨆ m : ℕ, (⟪e, x⟫_ℝ - 1 / ((m : ℝ) + 1)) = ⟪e, x⟫_ℝ :=
  tendsto_nhds_unique (tendsto_atTop_ciSup (monotone_inner_sub_one_div e x)
    ⟨⟪e, x⟫_ℝ, by rintro _ ⟨m, rfl⟩; simp only [sub_le_self_iff]; positivity⟩)
    ((tendstoUniformly_inner_sub_one_div e).tendsto_at x)

end TauCeti.Examples.HarnackAffine
