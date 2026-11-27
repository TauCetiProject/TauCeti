/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Topology.MetricSpace.BallCutoff
import TauCeti.Topology.MetricSpace.Holder

/-!
# Compactly supported extensions of Hölder maps on a closed ball

A map `f` that is `α`-Hölder on a closed ball `closedBall x₀ r` with `r > 0` and `α ≤ 1` agrees
there with a bounded, globally `α`-Hölder map supported in the doubled ball
`closedBall x₀ (2 * r)` (`HolderOnWith.exists_holderWith_eqOn_closedBall`).

The extension is `x ↦ χ x • f (ρ x)`. Here `ρ = TauCeti.centeredRadialRetraction x₀ r` pulls each
point back to the ball, which makes `f ∘ ρ` globally Hölder
(`HolderOnWith.comp_centeredRadialRetraction`), and the cutoff
`χ = TauCeti.ballCutoff x₀ r`, `χ x = projIcc 0 1 (2 - dist x x₀ / r)`, is Hölder
(`TauCeti.holderWith_ballCutoff`), equal to `1` on the ball and `0` off the doubled ball. The
product of the two bounded Hölder maps is Hölder (`HolderWith.smul_of_eq_zero`).

Integral operators such as the planar Cauchy transform act on compactly supported Hölder sources,
so this extension lets them act on data given only on a closed disc.
-/

public section

open Function Metric Set
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SeminormedAddCommGroup F]
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
  -- The cutoff `χ` is Hölder with values in `[0, 1]`.
  set χ := TauCeti.ballCutoff x₀ r
  have hχb (x : E) : ‖χ x‖ ≤ (1 : ℝ≥0) := TauCeti.norm_ballCutoff_le x₀ r x
  have hχ := TauCeti.holderWith_ballCutoff x₀ r hα
  refine ⟨fun x ↦ χ x • f (ρ x), _, 1 * M.toNNReal,
    HolderWith.smul_of_eq_zero hχ (hfρ.holderOnWith univ) hχb (fun x _ ↦ hfρM x)
      (fun x hx ↦ (hx (mem_univ x)).elim), fun x ↦ ?_, ?_, fun x hx ↦ ?_⟩
  · rw [norm_smul, NNReal.coe_mul]
    exact mul_le_mul (hχb x) (hfρM x) (norm_nonneg _) zero_le_one
  · refine support_subset_iff'.2 fun x hx ↦ ?_
    rw [mem_closedBall, not_le] at hx
    simp only [χ, TauCeti.ballCutoff_eq_zero_of_two_mul_le_dist hr hx.le, zero_smul]
  · simp only [χ, TauCeti.ballCutoff_eq_one_of_mem_closedBall hr hx, one_smul, ρ,
      TauCeti.centeredRadialRetraction_of_mem_closedBall hx]
