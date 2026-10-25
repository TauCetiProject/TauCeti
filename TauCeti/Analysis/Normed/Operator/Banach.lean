/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Exact preimages from approximate preimages

Banach's open mapping theorem is proved in two steps. Baire's theorem first shows that every
point of the target is approximately the image of a point of controlled norm; a geometric
series then upgrades these approximate preimages to exact ones, using completeness of the
domain. Mathlib only states the composite theorem
`ContinuousLinearMap.exists_preimage_norm_le`, whose hypothesis is surjectivity.

This file isolates the second step, so that other sources of approximate preimages can be fed
into it. The main application is the case where the closure of the image of every ball contains a
ball, as happens when the adjoint is bounded below; this is how surjectivity is recovered in the
closed-range theorem. The scalar actions need no compatibility with the norms; only additivity
and continuity of the map enter the argument.

## Main declarations

* `ContinuousLinearMap.exists_preimage_norm_le_of_approx`: approximate preimages of controlled
  norm with relative error `1 / 2` give exact preimages of controlled norm.
* `ContinuousLinearMap.exists_preimage_norm_le_of_mem_closure`: if every `y` lies in the closure of
  the image of the closed ball of radius `C * ‖y‖`, then every `y` has a preimage of norm at most
  `2 * C * ‖y‖`.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., Lemma 4.13.

The series argument follows the second half of the proof of Mathlib's
`ContinuousLinearMap.exists_preimage_norm_le`.
-/

public section

open Function Metric Set Filter Finset Topology

namespace ContinuousLinearMap

variable {𝕜 𝕜' : Type*} [Semiring 𝕜] [Semiring 𝕜'] {σ : 𝕜 →+* 𝕜'}
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [Module 𝕜' F]

/-- **Approximate preimages give exact preimages.** If every `y` is within `‖y‖ / 2` of the
image of a point of norm at most `C * ‖y‖`, then every `y` is the image of a point of norm at
most `2 * C * ‖y‖`. -/
theorem exists_preimage_norm_le_of_approx (f : E →SL[σ] F) {C : ℝ}
    (hC : ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) (y : F) :
    ∃ x, f x = y ∧ ‖x‖ ≤ 2 * C * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  have hC0 : 0 ≤ C := by
    obtain ⟨x₀, -, hx₀⟩ := hC y
    by_contra hneg
    nlinarith [norm_nonneg x₀, norm_pos_iff.2 hy]
  /- Let `g y` be the approximate preimage of `y`, and `h y = y - f (g y)` the part of `y` that
  is not yet hit. Iterating, `u n = g (h^[n] y)` is a summable series whose sum is a preimage
  of `y`. -/
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [iterate_succ']
      apply (hle _).trans
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    calc
      ‖u n‖ ≤ C * ‖h^[n] y‖ := (hg _).2
      _ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n ↦ ‖u n‖ :=
    .of_nonneg_of_le (fun n ↦ norm_nonneg _) ule
      (Summable.mul_right _ summable_geometric_two)
  let x := tsum u
  have x_ineq : ‖x‖ ≤ 2 * C * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n IH => rw [sum_range_succ, map_add, IH, iterate_succ_apply', sub_add]
  have L₁ : Tendsto (fun n ↦ f (∑ i ∈ range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp sNu.of_norm.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n ↦ y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  exact ⟨x, by simpa using tendsto_nhds_unique L₁ L₂, x_ineq⟩

/-- **Banach's lemma.** If every `y` lies in the closure of the image of the closed ball of radius
`C * ‖y‖`, then every `y` has a preimage of norm at most `2 * C * ‖y‖`. In particular, the
map is surjective. -/
theorem exists_preimage_norm_le_of_mem_closure (f : E →SL[σ] F) {C : ℝ}
    (hC : ∀ y, y ∈ closure (f '' closedBall 0 (C * ‖y‖))) (y : F) :
    ∃ x, f x = y ∧ ‖x‖ ≤ 2 * C * ‖y‖ := by
  refine f.exists_preimage_norm_le_of_approx (fun y ↦ ?_) y
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp, by simp⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ :=
    Metric.mem_closure_iff.mp (hC y) (1 / 2 * ‖y‖) (by positivity)
  refine ⟨x, ?_, ?_⟩
  · rw [dist_comm]
    exact hxy.le
  · simpa using hx

end ContinuousLinearMap
