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
`χ = TauCeti.ballCutoff x₀ r`, `χ x = projIcc 0 1 (2 - dist x x₀ / r)`, is Lipschitz
(`TauCeti.lipschitzWith_ballCutoff`), equal to `1` on the ball and `0` off the doubled ball. The
product of the two bounded Hölder maps is Hölder (`HolderWith.smul_of_eq_zero`).

Integral operators such as the planar Cauchy transform act on compactly supported Hölder sources,
so this extension lets them act on data given only on a closed disc.
-/

public section

open Function Metric Set
open scoped NNReal

namespace TauCeti

section Cutoff

variable {X : Type*} [PseudoMetricSpace X] {x₀ x : X} {r : ℝ}

/-- The cutoff of the closed ball `closedBall x₀ r`, `x ↦ projIcc 0 1 (2 - dist x x₀ / r)`: for
`r > 0` it is `1` on the ball, `0` off the doubled ball and `r⁻¹`-Lipschitz, with values in
`[0, 1]`. -/
noncomputable def ballCutoff (x₀ : X) (r : ℝ) (x : X) : ℝ :=
  (projIcc (0 : ℝ) 1 zero_le_one (2 - dist x x₀ / r) : ℝ)

theorem ballCutoff_apply (x₀ : X) (r : ℝ) (x : X) :
    ballCutoff x₀ r x = projIcc (0 : ℝ) 1 zero_le_one (2 - dist x x₀ / r) := by
  rw [ballCutoff]

/-- The ball cutoff is `1` on its closed ball. -/
theorem ballCutoff_eq_one_of_mem_closedBall (hr : 0 < r) (hx : x ∈ closedBall x₀ r) :
    ballCutoff x₀ r x = 1 := by
  have hone : 1 ≤ 2 - dist x x₀ / r := by
    rw [le_sub_comm, div_le_iff₀ hr]
    linarith [mem_closedBall.mp hx]
  rw [ballCutoff, projIcc_of_right_le _ hone]

/-- The ball cutoff vanishes off the doubled ball. -/
theorem ballCutoff_eq_zero_of_two_mul_le_dist (hr : 0 < r) (hx : 2 * r ≤ dist x x₀) :
    ballCutoff x₀ r x = 0 := by
  have hneg : 2 - dist x x₀ / r ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hr]
    linarith
  rw [ballCutoff, projIcc_of_le_left _ hneg]

/-- The ball cutoff takes values in `[0, 1]`. -/
theorem norm_ballCutoff_le (x₀ : X) (r : ℝ) (x : X) : ‖ballCutoff x₀ r x‖ ≤ 1 := by
  have h := (projIcc (0 : ℝ) 1 zero_le_one (2 - dist x x₀ / r)).property
  rw [ballCutoff, Real.norm_of_nonneg h.1]
  exact h.2

/-- The ball cutoff of radius `r` is `|r|⁻¹`-Lipschitz. -/
theorem lipschitzWith_ballCutoff (x₀ : X) (r : ℝ) : LipschitzWith ‖r‖₊⁻¹ (ballCutoff x₀ r) := by
  have hlin : LipschitzWith ‖r‖₊⁻¹ fun x : X ↦ 2 - dist x x₀ / r :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [Real.dist_eq, NNReal.coe_inv, coe_nnNorm, Real.norm_eq_abs,
        show 2 - dist x x₀ / r - (2 - dist y x₀ / r) = r⁻¹ * (dist y x₀ - dist x x₀) by ring,
        abs_mul, abs_inv, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y x₀) (inv_nonneg.2 (abs_nonneg r))
  have h := (LipschitzWith.subtypeVal _).comp ((LipschitzWith.projIcc (zero_le_one' ℝ)).comp hlin)
  rw [one_mul, one_mul] at h
  exact h

end Cutoff

end TauCeti

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
  -- The cutoff `χ` is Lipschitz with values in `[0, 1]`, hence Hölder.
  set χ := TauCeti.ballCutoff x₀ r
  have hχb (x : E) : ‖χ x‖ ≤ (1 : ℝ≥0) := TauCeti.norm_ballCutoff_le x₀ r x
  have hχ := holderOnWith_univ.mp ((TauCeti.lipschitzWith_ballCutoff x₀ r).lipschitzOnWith
    |>.holderOnWith_of_norm_le (fun x _ ↦ hχb x) hα)
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
