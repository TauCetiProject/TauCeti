/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder bounds for lower-order terms

On a ball `B(x, R)` of radius `R ≤ 1` in a real normed space, let `u` be `C²` with `|u|`, `‖Du‖`
and `‖D²u‖` bounded by `N`, and let `b` and `c` be `α`-Hölder for some `α ≤ 1`. Then the
lower-order part `y ↦ Du(y) (b y) + c(y) u(y)` of a second-order operator is `α`-Hölder on the
ball with constant `D N`, where `D` depends only on `α`, the Hölder constant of `b` and `c`, and
their values at the centre (`TauCeti.exists_holderOnWith_fderiv_apply_add_mul_ball`). This is
how lower-order terms are absorbed in Schauder estimates.

The functions `u` and `Du` are `N`-Lipschitz on the convex ball `B(x, R)`, whose diameter is at most
`2R`, hence `α`-Hölder with constant `N (2R)^{1-α}`
(`TauCeti.holderOnWith_and_holderOnWith_fderiv_ball_of_norm_le`). The two products are then
Hölder by the bilinear estimate `ContinuousLinearMap.holderOnWith_comp₂`, applied to evaluation
and multiplication.
-/

public section

open Metric Set
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On the ball `B(x, R)`, a `C²` function `u` with `‖Du‖ ≤ N` and `‖D²u‖ ≤ N`, and its derivative
`Du`, are `α`-Hölder with constant `N (2R)^{1-α}`: they are `N`-Lipschitz on the convex ball, whose
diameter is at most `2R`. -/
theorem holderOnWith_and_holderOnWith_fderiv_ball_of_norm_le {u : E → ℝ} {x : E} {R : ℝ}
    {N α : ℝ≥0} (hα : α ≤ 1) (hu : ContDiffOn ℝ 2 u (ball x R))
    (hN₁ : ∀ y ∈ ball x R, ‖fderiv ℝ u y‖ ≤ N)
    (hN₂ : ∀ y ∈ ball x R, ‖iteratedFDeriv ℝ 2 u y‖ ≤ N) :
    HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α u (ball x R) ∧
      HolderOnWith (N * (2 * R).toNNReal ^ ((1 : ℝ) - α)) α (fderiv ℝ u) (ball x R) := by
  have hdiam : ∀ y ∈ ball x R, ∀ z ∈ ball x R, edist y z ≤ (2 * R).toNNReal := by
    intro y hy z hz
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith [dist_triangle_right y z x, mem_ball.1 hy, mem_ball.1 hz]
  have hcda (y : E) (hy : y ∈ ball x R) : ContDiffAt ℝ 2 u y :=
    hu.contDiffAt (isOpen_ball.mem_nhds hy)
  have hLu : LipschitzOnWith N u (ball x R) :=
    (convex_ball x R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y hy => (hcda y hy).differentiableAt (by norm_num))
      fun y hy => by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hN₁ y hy
  have hLDu : LipschitzOnWith N (fderiv ℝ u) (ball x R) :=
    (convex_ball x R).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y hy => ((hcda y hy).fderiv_right (m := 1) le_rfl).differentiableAt (by norm_num))
      fun y hy => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
        exact hN₂ y hy
  exact ⟨by simpa using (holderOnWith_one.2 hLu).of_le hdiam hα,
    by simpa using (holderOnWith_one.2 hLDu).of_le hdiam hα⟩

/-- On a ball of radius at most one, the lower-order part `y ↦ Du(y) (b y) + c(y) u(y)` of a `C²`
function `u` with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` there is `α`-Hölder with constant
`D N`, when `b` and `c` are `α`-Hölder on the ball. The constant `D` depends only on `α`, the
Hölder constant of `b` and `c`, and their values at the centre. -/
theorem exists_holderOnWith_fderiv_apply_add_mul_ball {α : ℝ≥0} (hα : α ≤ 1) {x : E}
    {R : ℝ} (hR : R ≤ 1) {b : E → E} {c : E → ℝ} {L : ℝ≥0} (hb : HolderOnWith L α b (ball x R))
    (hc : HolderOnWith L α c (ball x R)) :
    ∃ D : ℝ≥0, ∀ {u : E → ℝ} {N : ℝ≥0}, ContDiffOn ℝ 2 u (ball x R) →
      (∀ y ∈ ball x R, |u y| ≤ N) → (∀ y ∈ ball x R, ‖fderiv ℝ u y‖ ≤ N) →
      (∀ y ∈ ball x R, ‖iteratedFDeriv ℝ 2 u y‖ ≤ N) →
      HolderOnWith (D * N) α (fun y => fderiv ℝ u y (b y) + c y * u y) (ball x R) := by
  set κ : ℝ≥0 := 2 ^ ((1 : ℝ) - α)
  set β : ℝ≥0 := ‖b x‖₊ + L
  set γ : ℝ≥0 := ‖c x‖₊ + L
  refine ⟨β * κ + L + (γ * κ + L), fun {u N} hu hN₀ hN₁ hN₂ => ?_⟩
  -- On the ball, `b` and `c` stay within `L R^α ≤ L` of their values at the centre.
  have hbM : ∀ y ∈ ball x R, ‖b y‖ ≤ β := fun y hy => by
    have h1 := hb.dist_le_mul_rpow_of_mem_ball hy
    have h2 : R ^ (α : ℝ) ≤ 1 :=
      Real.rpow_le_one (dist_nonneg.trans (mem_ball.1 hy).le) hR α.coe_nonneg
    have h3 := norm_le_norm_add_norm_sub' (b y) (b x)
    rw [← dist_eq_norm] at h3
    simp only [β, NNReal.coe_add, coe_nnnorm]
    nlinarith [L.coe_nonneg]
  have hcM : ∀ y ∈ ball x R, ‖c y‖ ≤ γ := fun y hy => by
    have h1 := hc.dist_le_mul_rpow_of_mem_ball hy
    have h2 : R ^ (α : ℝ) ≤ 1 :=
      Real.rpow_le_one (dist_nonneg.trans (mem_ball.1 hy).le) hR α.coe_nonneg
    have h3 := norm_le_norm_add_norm_sub' (c y) (c x)
    rw [← dist_eq_norm] at h3
    simp only [γ, NNReal.coe_add, coe_nnnorm]
    nlinarith [L.coe_nonneg]
  -- `u` and `Du` are `α`-Hölder with constant `N (2R)^{1-α} ≤ N κ`, as `2R ≤ 2`.
  have hκ : N * (2 * R).toNNReal ^ ((1 : ℝ) - α) ≤ N * κ := by
    refine mul_le_mul_right (NNReal.rpow_le_rpow ?_ (sub_nonneg.2 (by exact_mod_cast hα))) N
    rw [Real.toNNReal_le_iff_le_coe]
    push_cast
    linarith
  obtain ⟨hHu, hHDu⟩ := holderOnWith_and_holderOnWith_fderiv_ball_of_norm_le hα hu hN₁ hN₂
  replace hHu := hHu.mono_const hκ
  replace hHDu := hHDu.mono_const hκ
  -- Both products are Hölder by the bilinear estimate, applied to evaluation and multiplication.
  have h1 : HolderOnWith (N * L + β * (N * κ)) α (fun y => fderiv ℝ u y (b y)) (ball x R) :=
    ((ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).holderOnWith_comp₂ hHDu hb hN₁ hbM).mono_const
      (mul_le_of_le_one_left' ContinuousLinearMap.norm_id_le)
  have h2 : HolderOnWith (γ * (N * κ) + N * L) α (fun y => c y * u y) (ball x R) :=
    ((ContinuousLinearMap.mul ℝ ℝ).holderOnWith_comp₂ hc hHu hcM
      (fun y hy => by simpa only [Real.norm_eq_abs] using hN₀ y hy)).mono_const
      (mul_le_of_le_one_left' (ContinuousLinearMap.opNorm_mul_le ℝ ℝ))
  exact (HolderWith.restrict_iff.1 (h1.holderWith.add h2.holderWith)).mono_const
    (le_of_eq (by ring))

end TauCeti
