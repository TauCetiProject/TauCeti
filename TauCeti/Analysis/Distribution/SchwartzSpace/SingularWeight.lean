/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Schwartz functions against singular power weights

Let `E` be a finite-dimensional real normed space of dimension `d ≥ 1` with an additive Haar
measure `μ`. The weight `‖x‖ ^ t` is locally integrable exactly when `-d < t`; it may be singular
at `0`, and it grows polynomially at infinity. A Schwartz function absorbs the growth, so for every
real `t > -d` the function `‖x‖ ^ t ‖f x‖` is integrable, and its integral is bounded by a finite
supremum of Schwartz seminorms of `f`. Consequently integration against such a weight is a
continuous functional on the Schwartz space.

The case `t ≥ 0`, for every measure of temperate growth, is
`SchwartzMap.integrable_norm_rpow_mul_norm`. The negative exponents are those of the archimedean
local zeta integrals: `∫ f(x) |x| ^ (s - 1) dx` over `ℝ` and `∫ f(z) |z| ^ (2 s - 2) dz` over `ℂ`
converge for every Schwartz `f` exactly on `0 < re s`.

## Main results

* `integrable_norm_rpow_mul_one_add_norm_rpow_neg`: `‖x‖ ^ t (1 + ‖x‖) ^ (-r)` is integrable for
  `-d < t` and `|t| + d < r`.
* `SchwartzMap.integrable_norm_rpow_mul_norm_of_neg_finrank_lt`: `‖x‖ ^ t ‖f x‖` is integrable for
  every Schwartz `f` and `-d < t`.
* `SchwartzMap.exists_integral_norm_rpow_mul_norm_le`: `∫ ‖x‖ ^ t ‖f x‖ dμ` is bounded by a
  constant times a finite supremum of Schwartz seminorms of `f`.
-/

public section

open MeasureTheory Metric Module Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- On a finite-dimensional real normed space of dimension `d ≥ 1`, the weight
`‖x‖ ^ t (1 + ‖x‖) ^ (-r)` is integrable for every Haar measure when `-d < t` (integrability at
`0`) and `|t| + d < r` (integrability at infinity). -/
theorem integrable_norm_rpow_mul_one_add_norm_rpow_neg {t r : ℝ}
    (ht : -(finrank ℝ E : ℝ) < t) (hr : |t| + finrank ℝ E < r) :
    Integrable (fun x : E ↦ ‖x‖ ^ t * (1 + ‖x‖) ^ (-r)) μ := by
  have hd : 1 ≤ finrank ℝ E := Nat.one_le_iff_ne_zero.2 (finrank_pos (R := ℝ) (M := E)).ne'
  have hr0 : 0 ≤ r := by linarith [abs_nonneg t, (Nat.cast_nonneg (finrank ℝ E) : (0 : ℝ) ≤ _)]
  have hmeas : AEStronglyMeasurable (fun x : E ↦ ‖x‖ ^ t * (1 + ‖x‖) ^ (-r)) μ :=
    ((measurable_norm.pow_const t).mul
      ((measurable_const.add measurable_norm).pow_const (-r))).aestronglyMeasurable
  have hφ (x : E) : 0 ≤ ‖x‖ ^ t * (1 + ‖x‖) ^ (-r) := by positivity
  rw [← integrableOn_univ, ← union_compl_self (ball (0 : E) 1)]
  refine IntegrableOn.union ?_ ?_
  · -- Near `0` the weight is at most `‖x‖ ^ t`.
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := -t) hd (by linarith)
      (ae_of_all _ fun x ↦ ?_) hmeas
    rw [Real.norm_of_nonneg (hφ x), neg_neg, one_mul]
    exact mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith))
  · -- Away from `0`, `‖x‖ ^ t ≤ (1 + ‖x‖) ^ |t|`.
    refine ((integrable_one_add_norm (μ := μ) (r := r - |t|) (by linarith)).integrableOn).mono'
      hmeas.restrict ((ae_restrict_mem measurableSet_ball.compl).mono fun x hx ↦ ?_)
    have hx1 : 1 ≤ ‖x‖ := by simpa using hx
    have hpos : 0 < 1 + ‖x‖ := by positivity
    have key : ‖x‖ ^ t ≤ (1 + ‖x‖) ^ |t| := by
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h]
        exact Real.rpow_le_rpow (norm_nonneg x) (by linarith) h
      · exact (Real.rpow_le_one_of_one_le_of_nonpos hx1 h).trans
          (Real.one_le_rpow (x := 1 + ‖x‖) (by linarith) (abs_nonneg t))
    calc ‖‖x‖ ^ t * (1 + ‖x‖) ^ (-r)‖ = ‖x‖ ^ t * (1 + ‖x‖) ^ (-r) := Real.norm_of_nonneg (hφ x)
      _ ≤ (1 + ‖x‖) ^ |t| * (1 + ‖x‖) ^ (-r) := mul_le_mul_of_nonneg_right key (by positivity)
      _ = (1 + ‖x‖) ^ (-(r - |t|)) := by rw [← Real.rpow_add hpos]; ring_nf

namespace SchwartzMap

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The Schwartz decay bound `‖x‖ ^ t ‖f x‖ ≤ 2 ^ m S(f) ‖x‖ ^ t (1 + ‖x‖) ^ (-m)`, where `S` is
the supremum of the seminorms of index at most `(m, 0)`. -/
private theorem norm_rpow_mul_norm_le (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] (f : 𝓢(E, F)) (t : ℝ) (m : ℕ) (x : E) :
    ‖x‖ ^ t * ‖f x‖ ≤ 2 ^ m * (Finset.Iic (m, 0)).sup (schwartzSeminormFamily 𝕜 E F) f *
      (‖x‖ ^ t * (1 + ‖x‖) ^ (-(m : ℝ))) := by
  have hpos : 0 < 1 + ‖x‖ := by positivity
  have h := f.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (m, 0)) le_rfl le_rfl x
  rw [norm_iteratedFDeriv_zero] at h
  rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
  calc ‖x‖ ^ t * ‖f x‖ = ‖x‖ ^ t * ((1 + ‖x‖) ^ m * ‖f x‖) * ((1 + ‖x‖) ^ m)⁻¹ := by
        field_simp
    _ ≤ ‖x‖ ^ t * (2 ^ m * (Finset.Iic (m, 0)).sup (schwartzSeminormFamily 𝕜 E F) f) *
        ((1 + ‖x‖) ^ m)⁻¹ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by positivity)) ?_
        positivity
    _ = _ := by ring

/-- **Integrability against a singular power weight.** For a Schwartz function `f` on a
finite-dimensional real normed space of dimension `d ≥ 1` and a real `t > -d`, the function
`‖x‖ ^ t ‖f x‖` is integrable for every Haar measure. -/
theorem integrable_norm_rpow_mul_norm_of_neg_finrank_lt (f : 𝓢(E, F)) {t : ℝ}
    (ht : -(finrank ℝ E : ℝ) < t) :
    Integrable (fun x ↦ ‖x‖ ^ t * ‖f x‖) μ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (|t| + finrank ℝ E)
  refine ((integrable_norm_rpow_mul_one_add_norm_rpow_neg μ ht hm).const_mul
    (2 ^ m * (Finset.Iic (m, 0)).sup (schwartzSeminormFamily ℝ E F) f)).mono'
    ((measurable_norm.pow_const t).aestronglyMeasurable.mul
      f.continuous.norm.aestronglyMeasurable) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact norm_rpow_mul_norm_le ℝ f t m x

/-- **The singular power weight is a continuous functional.** For a real `t > -d`, the integral
`∫ ‖x‖ ^ t ‖f x‖ dμ` is bounded by a constant times a finite supremum of Schwartz seminorms of
`f`. -/
theorem exists_integral_norm_rpow_mul_norm_le (𝕜 : Type*) [RCLike 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] {t : ℝ} (ht : -(finrank ℝ E : ℝ) < t) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : 𝓢(E, F),
      ∫ x, ‖x‖ ^ t * ‖f x‖ ∂μ ≤ C * s.sup (schwartzSeminormFamily 𝕜 E F) f := by
  obtain ⟨m, hm⟩ := exists_nat_gt (|t| + finrank ℝ E)
  have hint := integrable_norm_rpow_mul_one_add_norm_rpow_neg μ ht hm
  refine ⟨Finset.Iic (m, 0), 2 ^ m * ∫ x, ‖x‖ ^ t * (1 + ‖x‖) ^ (-(m : ℝ)) ∂μ,
    mul_nonneg (by positivity) (integral_nonneg fun x ↦ by positivity), fun f ↦ ?_⟩
  calc ∫ x, ‖x‖ ^ t * ‖f x‖ ∂μ
      ≤ ∫ x, 2 ^ m * (Finset.Iic (m, 0)).sup (schwartzSeminormFamily 𝕜 E F) f *
          (‖x‖ ^ t * (1 + ‖x‖) ^ (-(m : ℝ))) ∂μ :=
        integral_mono (f.integrable_norm_rpow_mul_norm_of_neg_finrank_lt μ ht)
          (hint.const_mul _) fun x ↦ norm_rpow_mul_norm_le 𝕜 f t m x
    _ = _ := by rw [integral_const_mul]; ring

end SchwartzMap
