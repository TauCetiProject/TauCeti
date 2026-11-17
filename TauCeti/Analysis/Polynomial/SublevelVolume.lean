/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Small sublevel sets of monic complex polynomials

For a monic complex polynomial `∏ i, (X - a i)` with `n` roots, the set where its modulus is less
than `δ` lies in the union of the discs of radius `δ ^ (1 / n)` about the roots. Its Lebesgue
measure is therefore small for small `δ`, uniformly in the roots.

## Main results

* `TauCeti.exists_volume_setOf_norm_eval_prod_lt_le`: for every `η > 0` there is `δ > 0` such
  that `{z | ‖∏ i, (z - a i)‖ < δ}` has measure at most `η` for every family of roots `a`.
-/

public section

namespace TauCeti

open MeasureTheory Metric Polynomial Set

variable {ι : Type*} [Fintype ι]

/-- **Small sublevel sets.** The set where `‖∏ i, (z - a i)‖ < δ` has measure at most `η` for
`δ` small enough, uniformly in the roots: it lies in the union of the discs of radius `δ ^ (1/n)`
about the roots. -/
theorem exists_volume_setOf_norm_eval_prod_lt_le [Nonempty ι] {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ a : ι → ℂ,
      volume {z | ‖(∏ i, (X - C (a i))).eval z‖ < δ} ≤ ENNReal.ofReal η := by
  set n := Fintype.card ι
  have hn : (0 : ℝ) < n := by exact_mod_cast Fintype.card_pos
  set ρ := √(η / (4 * n))
  have hρ : 0 < ρ := Real.sqrt_pos.2 (by positivity)
  refine ⟨ρ ^ n, by positivity, fun a ↦ ?_⟩
  have hsub : {z | ‖(∏ i, (X - C (a i))).eval z‖ < ρ ^ n} ⊆ ⋃ i, ball (a i) ρ := by
    intro z hz
    simp only [mem_ofPred_eq, eval_prod, eval_sub, eval_X, eval_C, norm_prod] at hz
    by_contra hzU
    simp only [mem_iUnion, mem_ball, not_exists, not_lt, dist_eq_norm] at hzU
    have : ρ ^ n ≤ ∏ i, ‖z - a i‖ := by
      calc ρ ^ n = ∏ _i : ι, ρ := by rw [Finset.prod_const, Finset.card_univ]
        _ ≤ ∏ i, ‖z - a i‖ := Finset.prod_le_prod₀ (fun _ _ ↦ hρ.le) fun i _ ↦ hzU i
    linarith
  have hball (i : ι) : volume (ball (a i) ρ) = ENNReal.ofReal (ρ ^ 2 * Real.pi) := by
    rw [Complex.volume_ball, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hρ.le,
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  calc volume {z | ‖(∏ i, (X - C (a i))).eval z‖ < ρ ^ n}
      ≤ volume (⋃ i, ball (a i) ρ) := measure_mono hsub
    _ ≤ ∑ i, volume (ball (a i) ρ) := measure_iUnion_fintype_le _ _
    _ = ENNReal.ofReal (n * (ρ ^ 2 * Real.pi)) := by
      simp only [hball, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ n), ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ρ ^ 2)]
    _ ≤ ENNReal.ofReal η := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.sq_sqrt (by positivity)]
      have := Real.pi_lt_four
      have hn' : (n : ℝ) ≠ 0 := hn.ne'
      field_simp
      nlinarith

end TauCeti
