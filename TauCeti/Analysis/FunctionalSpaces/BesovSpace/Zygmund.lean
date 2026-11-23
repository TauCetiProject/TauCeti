/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Zygmund
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# The Zygmund class `𝒞¹` is larger than the Lipschitz functions

For non-integer `s = k + α` the Hölder–Zygmund space `𝒞^s = B^s_{∞,∞}` is the bounded Hölder space
`C_b^{k,α}` (`TauCeti.BesovSpace.ckHolderSpaceEquiv`). At integer order this fails. This file
shows it at `s = 1` on the line: there is an element of `𝒞¹(ℝ)` that is a bounded continuous
function with no Lipschitz representative
(`TauCeti.BesovSpace.exists_toDistr_eq_toLpTop_and_forall_lipschitzWith_toDistr_ne`), so
`𝒞¹ ≠ C_b^{0,1}` and the non-integer hypothesis of the identification is load-bearing.

The witness is the second difference of `x log |x|` with step `1`,

`ζ(t) = (t + 1) log |t + 1| + (t - 1) log |t - 1| - 2 t log |t|`

(in Lean `Real.log` already takes the absolute value). It is continuous, and bounded since the
second differences of `x log |x|` are `O(|h|)`
(`Real.abs_add_mul_log_add_add_sub_mul_log_sub_sub_two_mul_mul_log_le`, at `h = 1`). For the same
reason, being a combination of three translates of `x log |x|`, it satisfies Zygmund's condition
`|ζ(x + h) + ζ(x - h) - 2 ζ(x)| ≤ C |h|`, so it lies in `𝒞¹`
(`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_norm_add_add_sub_two_nsmul_le`). Near `0`
it behaves like `-2 t log t`: for `0 < t < 1`, `ζ(t) ≥ -2 t log t` and `ζ(0) = 0`, so its
difference quotients at `0` are unbounded and it is not Lipschitz. A bounded continuous function
is determined by its tempered distribution, so no Lipschitz function represents the same element
of `𝒞¹`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
* A. Zygmund, *Smooth functions*, Duke Math. J. 12 (1945), 47–76.
-/

public section

noncomputable section

open MeasureTheory Real BoundedContinuousFunction
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti

/-- The second difference of `x log |x|` with step `1`, a bounded function in the Zygmund class
that is not Lipschitz at `0`. -/
private def zygmundWitness (t : ℝ) : ℝ :=
  (t + 1) * log (t + 1) + (t - 1) * log (t - 1) - 2 * (t * log t)

private theorem continuous_zygmundWitness : Continuous zygmundWitness := by
  unfold zygmundWitness
  fun_prop

private theorem abs_zygmundWitness_le (t : ℝ) : |zygmundWitness t| ≤ 30 := by
  simpa [zygmundWitness, add_sub_cancel_right] using
    abs_add_mul_log_add_add_sub_mul_log_sub_sub_two_mul_mul_log_le t 1

/-- The witness satisfies Zygmund's condition. -/
private theorem abs_zygmundWitness_add_add_sub_two_mul_le (x h : ℝ) :
    |zygmundWitness (x + h) + zygmundWitness (x - h) - 2 * zygmundWitness x| ≤ 120 * |h| := by
  -- The witness is a combination of three translates of `x log |x|`, each of whose second
  -- differences is at most `30 |h|`.
  have hD (y : ℝ) := abs_add_mul_log_add_add_sub_mul_log_sub_sub_two_mul_mul_log_le y h
  set D : ℝ → ℝ := fun y ↦ (y + h) * log (y + h) + (y - h) * log (y - h) - 2 * (y * log y)
  have heq : zygmundWitness (x + h) + zygmundWitness (x - h) - 2 * zygmundWitness x =
      D (x + 1) + D (x - 1) - 2 * D x := by
    simp only [zygmundWitness, D]
    rw [show x + h + 1 = x + 1 + h by ring, show x + h - 1 = x - 1 + h by ring,
      show x - h + 1 = x + 1 - h by ring, show x - h - 1 = x - 1 - h by ring]
    ring
  rw [heq]
  have h₁ := hD (x + 1)
  have h₂ := hD (x - 1)
  have h₃ := hD x
  calc |D (x + 1) + D (x - 1) - 2 * D x| ≤ |D (x + 1)| + |D (x - 1)| + 2 * |D x| := by
        simpa [sub_eq_add_neg, abs_mul] using abs_add_three (D (x + 1)) (D (x - 1)) (-(2 * D x))
    _ ≤ 120 * |h| := by linarith

private theorem zygmundWitness_zero : zygmundWitness 0 = 0 := by
  simp [zygmundWitness, log_neg_eq_log]

/-- Near `0` the witness dominates `-2 t log t`. -/
private theorem neg_two_mul_mul_log_le_zygmundWitness {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    -2 * (t * log t) ≤ zygmundWitness t := by
  -- The two outer terms `(1 + t) log (1 + t) - (1 - t) log (1 - t)` are at least `2 t - t² ≥ 0`.
  have hp : 0 < t + 1 := by linarith
  have hm : 0 < 1 - t := by linarith
  -- `u ≤ (1 + u) log (1 + u) ≤ u + u²` for `u > -1`, from `1 - 1 / y ≤ log y ≤ y - 1`.
  have hlow : t ≤ (t + 1) * log (t + 1) := by
    have := one_sub_inv_le_log_of_pos hp
    have hmul := mul_le_mul_of_nonneg_left this hp.le
    rwa [mul_sub, mul_one, mul_inv_cancel₀ hp.ne', add_sub_cancel_right] at hmul
  have hup : (1 - t) * log (1 - t) ≤ -t + t ^ 2 := by
    have := log_le_sub_one_of_pos hm
    nlinarith [mul_le_mul_of_nonneg_left this hm.le]
  have hneg : (t - 1) * log (t - 1) = -((1 - t) * log (1 - t)) := by
    rw [show t - 1 = -(1 - t) by ring, log_neg_eq_log]
    ring
  rw [zygmundWitness, hneg]
  nlinarith

/-- The witness is not Lipschitz. -/
private theorem not_lipschitzWith_zygmundWitness (K : ℝ≥0) :
    ¬ LipschitzWith K (fun t ↦ (zygmundWitness t : ℂ)) := by
  -- Its difference quotient at `0` is at least `2 (K + 1)` at `t = exp (-(K + 1))`.
  intro hK
  set t := exp (-((K : ℝ) + 1))
  have ht0 : 0 < t := exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith [K.coe_nonneg])
  have hlog : log t = -((K : ℝ) + 1) := log_exp _
  have hdist : |zygmundWitness t| ≤ K * t := by
    simpa [Complex.dist_eq, ← Complex.ofReal_sub, zygmundWitness_zero, abs_of_pos ht0] using
      hK.dist_le_mul t 0
  have hlow := neg_two_mul_mul_log_le_zygmundWitness ht0 ht1
  rw [hlog] at hlow
  have := le_abs_self (zygmundWitness t)
  nlinarith [K.coe_nonneg]

namespace BesovSpace

/-- **The Zygmund class `𝒞¹` contains non-Lipschitz functions.** For every Littlewood–Paley bump
function `ψ` on `ℝ` there is an element `w` of the Hölder–Zygmund space `𝒞¹ = B¹_{∞,∞}` which is a
bounded continuous function `f`, but which no Lipschitz bounded continuous function represents.
So `𝒞¹ ≠ C_b^{0,1}`, unlike the identification `𝒞^{k+α} = C_b^{k,α}` at non-integer order. -/
theorem exists_toDistr_eq_toLpTop_and_forall_lipschitzWith_toDistr_ne (ψ : ContDiffBump (0 : ℝ)) :
    ∃ (f : ℝ →ᵇ ℂ) (w : BesovSpace ℂ ψ 1 ∞ ∞), w.toDistr = toLpTop volume ℂ f ∧
      ∀ (K : ℝ≥0) (g : ℝ →ᵇ ℂ), LipschitzWith K g → w.toDistr ≠ toLpTop volume ℂ g := by
  let f : ℝ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t ↦ (zygmundWitness t : ℂ)) (Complex.continuous_ofReal.comp continuous_zygmundWitness)
    30 fun t ↦ by simpa [Complex.norm_real] using abs_zygmundWitness_le t
  have hf (t : ℝ) : f t = zygmundWitness t := congrFun (coe_ofNormedAddCommGroup ..) t
  obtain ⟨C, -, hC⟩ := exists_toDistr_eq_and_norm_le_of_norm_add_add_sub_two_nsmul_le (F := ℂ) ψ 1
  obtain ⟨w, hw, -⟩ := hC f (H := 120) fun x h ↦ by
    have := abs_zygmundWitness_add_add_sub_two_mul_le x h
    rw [← norm_eq_abs, ← Complex.norm_real] at this
    simpa [hf, two_nsmul, ← two_mul] using this
  refine ⟨f, w, hw, fun K g hg heq ↦ not_lipschitzWith_zygmundWitness K ?_⟩
  have hfg : f = g :=
    BoundedContinuousFunction.toTemperedDistribution_toLpTop_injective (μ := volume)
      (hw.symm.trans heq)
  rw [hfg] at hf
  rwa [show (fun t ↦ (zygmundWitness t : ℂ)) = ⇑g from funext fun t ↦ (hf t).symm]

end BesovSpace

end TauCeti
