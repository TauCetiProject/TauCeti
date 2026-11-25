/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Order.ProjIcc
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Compactly supported extensions of Hölder maps on a closed ball

A map `f` that is `α`-Hölder on a closed ball `closedBall x₀ r` with `r > 0` and `α ≤ 1` agrees
there with a bounded, globally `α`-Hölder map supported in the doubled ball
`closedBall x₀ (2 * r)` (`HolderOnWith.exists_holderWith_eqOn_closedBall`).

The extension is `x ↦ χ x • f (ρ x)`. Here `ρ = TauCeti.centeredRadialRetraction x₀ r` pulls each
point back to the ball, which makes `f ∘ ρ` globally Hölder
(`HolderOnWith.comp_centeredRadialRetraction`), and the cutoff
`χ x = projIcc 0 1 (2 - dist x x₀ / r)` is Lipschitz, equal to `1` on the ball and `0` off the
doubled ball. The product of the two bounded Hölder maps is Hölder
(`HolderWith.smul_of_eq_zero`).

Integral operators such as the planar Cauchy transform act on compactly supported Hölder sources,
so this extension lets them act on data given only on a closed disc.
-/

public section

open Function Metric Set
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Hölder maps on a closed ball extend with compact support.** A map that is `α`-Hölder on the
closed ball `closedBall x₀ r`, with `0 < r` and `α ≤ 1`, agrees on that ball with a bounded,
globally `α`-Hölder map supported in `closedBall x₀ (2 * r)`. -/
theorem HolderOnWith.exists_holderWith_eqOn_closedBall {f : E → F} {C α : ℝ≥0} {x₀ : E} {r : ℝ}
    (hf : HolderOnWith C α f (closedBall x₀ r)) (hr : 0 < r) (hα : α ≤ 1) :
    ∃ (g : E → F) (H M : ℝ≥0), HolderWith H α g ∧ (∀ x, ‖g x‖ ≤ M) ∧
      support g ⊆ closedBall x₀ (2 * r) ∧ EqOn g f (closedBall x₀ r) := by
  set ρ := TauCeti.centeredRadialRetraction x₀ r
  -- The pulled-back map `f ∘ ρ` is globally Hölder and bounded by the bound of `f` on the ball.
  have hfρ := hf.comp_centeredRadialRetraction hr.le
  obtain ⟨M, hM⟩ := (hf.isBounded_image isBounded_closedBall).exists_norm_le
  have hfρM (x : E) : ‖f (ρ x)‖ ≤ M.toNNReal :=
    (hM _ (mem_image_of_mem f (TauCeti.centeredRadialRetraction_mem_closedBall hr.le x))).trans
      (Real.le_coe_toNNReal M)
  -- The cutoff `χ` is `r⁻¹`-Lipschitz with values in `[0, 1]`, hence Hölder.
  set χ : E → ℝ := fun x ↦ (projIcc (0 : ℝ) 1 zero_le_one (2 - dist x x₀ / r) : ℝ)
  have hlin : LipschitzWith r⁻¹.toNNReal fun x : E ↦ 2 - dist x x₀ / r :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hr.le),
        show 2 - dist x x₀ / r - (2 - dist y x₀ / r) = r⁻¹ * (dist y x₀ - dist x x₀) by ring,
        abs_mul, abs_of_pos (inv_pos.2 hr), abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y x₀) (inv_nonneg.2 hr.le)
  have hχL : LipschitzWith (1 * (1 * r⁻¹.toNNReal)) χ :=
    (LipschitzWith.subtypeVal _).comp ((LipschitzWith.projIcc (zero_le_one' ℝ)).comp hlin)
  have hχb (x : E) : ‖χ x‖ ≤ (1 : ℝ≥0) := by
    have h := (projIcc (0 : ℝ) 1 zero_le_one (2 - dist x x₀ / r)).property
    rw [Real.norm_of_nonneg h.1, NNReal.coe_one]
    exact h.2
  have hχ := holderOnWith_univ.mp (hχL.lipschitzOnWith.holderOnWith_of_norm_le
    (fun x _ ↦ hχb x) hα)
  refine ⟨fun x ↦ χ x • f (ρ x), _, 1 * M.toNNReal,
    HolderWith.smul_of_eq_zero hχ (hfρ.holderOnWith univ) hχb (fun x _ ↦ hfρM x)
      (fun x hx ↦ (hx (mem_univ x)).elim), fun x ↦ ?_, ?_, fun x hx ↦ ?_⟩
  · rw [norm_smul, NNReal.coe_mul]
    exact mul_le_mul (hχb x) (hfρM x) (norm_nonneg _) zero_le_one
  · refine support_subset_iff'.2 fun x hx ↦ ?_
    rw [mem_closedBall, not_le] at hx
    have hneg : 2 - dist x x₀ / r ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hr]
      linarith
    simp only [χ, projIcc_of_le_left _ hneg, zero_smul]
  · have hone : 1 ≤ 2 - dist x x₀ / r := by
      rw [le_sub_comm, div_le_iff₀ hr]
      linarith [mem_closedBall.mp hx]
    simp only [χ, projIcc_of_right_le _ hone, one_smul, ρ,
      TauCeti.centeredRadialRetraction_of_mem_closedBall hx]
