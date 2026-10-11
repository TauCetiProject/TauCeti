/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder
import TauCeti.Analysis.CompletelyMonotone.Bernstein.ExtremeRay
import TauCeti.MeasureTheory.Measure.Atom

/-!
# The extreme rays of the completely monotone cone

The functions that are continuous on `[0, ∞)` and completely monotone on `(0, ∞)` form a convex
cone. A nonzero function `f` in this cone spans an extreme ray exactly when it satisfies the
decomposition condition: every decomposition `f = g + h` inside the cone, compared on `[0, ∞)`,
has `g` a scalar multiple of `f`. This file shows that any `f` in the cone satisfying the
decomposition condition (including `f = 0`) is `t ↦ f 0 * exp (-(t * p))` on `[0, ∞)` for some
rate `p ≥ 0`: the exponentials are the only possible extreme rays. Conversely, every nonnegative
multiple of an exponential satisfies the decomposition condition, so the condition singles out
exactly the multiples of exponentials.

## Main declarations

* `TauCeti.IsContinuousCompletelyMonotoneOnIoi.exists_eq_mul_exp_neg_mul_of_extreme_ray`: a
  completely monotone function satisfying the decomposition condition (in particular, one spanning
  an extreme ray) is a nonnegative multiple of an exponential.
* `TauCeti.IsContinuousCompletelyMonotoneOnIoi.extreme_ray_iff_exists_eq_mul_exp_neg_mul`: a
  completely monotone function satisfies the decomposition condition if and only if it is a
  nonnegative multiple of an exponential on `[0, ∞)`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Chapter 1.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

namespace IsContinuousCompletelyMonotoneOnIoi

variable {f : ℝ → ℝ}

/-- **Extreme rays of the completely monotone cone are exponential.** Let `f` be continuous on
`[0, ∞)` and completely monotone on `(0, ∞)`, and suppose that whenever `f = g + h` on `[0, ∞)`
with `g` and `h` of the same kind, `g` is a scalar multiple of `f` on `[0, ∞)`. Then
`f t = f 0 * exp (-(t * p))` for all `t ≥ 0`, for some rate `p ≥ 0`. -/
theorem exists_eq_mul_exp_neg_mul_of_extreme_ray (hf : IsContinuousCompletelyMonotoneOnIoi f)
    (hext : ∀ g h : ℝ → ℝ, IsContinuousCompletelyMonotoneOnIoi g →
      IsContinuousCompletelyMonotoneOnIoi h → (∀ t : ℝ, 0 ≤ t → g t + h t = f t) →
        ∃ a : ℝ, ∀ t : ℝ, 0 ≤ t → g t = a * f t) :
    ∃ p : ℝ≥0, ∀ t : ℝ, 0 ≤ t → f t = f 0 * Real.exp (-(t * (p : ℝ))) := by
  set μ := bernsteinMeasure f
  have hμ : RepresentsLaplace μ f := representsLaplace_bernsteinMeasure hf
  have hrep (ν : Measure ℝ≥0) [IsFiniteMeasure ν] : RepresentsLaplace ν (laplaceTransform ν) :=
    representsLaplace_iff.mpr ⟨inferInstance, fun _ _ => rfl⟩
  -- Each restriction of `μ` represents a summand of `f`, hence is proportional to `μ`.
  have hrestrict (s : Set ℝ≥0) (hs : MeasurableSet s) :
      ∃ c : ℝ≥0∞, μ.restrict s = c • μ := by
    have hsum := (hrep (μ.restrict s)).add (hrep (μ.restrict sᶜ))
    rw [Measure.restrict_add_restrict_compl hs] at hsum
    obtain ⟨a, ha⟩ := hext _ _ (hrep _).isContinuousCompletelyMonotoneOnIoi
      (hrep _).isContinuousCompletelyMonotoneOnIoi
      fun t ht => (hsum.eq_laplaceTransform ht).trans (hμ.eq_laplaceTransform ht).symm
    rcases (hf.nonneg_zero).eq_or_lt with hf0 | hf0
    · -- If `f 0 = 0` then `μ` is the zero measure.
      have hμ0 : μ = 0 := by
        rw [← Measure.measure_univ_eq_zero, bernsteinMeasure_univ hf, ← hf0, ENNReal.ofReal_zero]
      exact ⟨0, by simp [hμ0]⟩
    have ha0 : 0 ≤ a := by
      have h0 := ha 0 le_rfl
      have hg0 : 0 ≤ laplaceTransform (μ.restrict s) 0 :=
        (hrep _).isContinuousCompletelyMonotoneOnIoi.nonneg_zero
      exact nonneg_of_mul_nonneg_left (h0 ▸ hg0) hf0
    let c : ℝ≥0 := ⟨a, ha0⟩
    exact ⟨c, (hrep (μ.restrict s)).unique ((hμ.smul c).congr fun t ht => ha t ht)⟩
  obtain ⟨p, hp⟩ := Measure.exists_eq_smul_dirac_of_forall_restrict_eq_smul μ hrestrict
  -- The point mass `μ univ • δ_p` represents `t ↦ f 0 * exp (-(t * p))`.
  have hdirac := (representsLaplace_dirac p).smul (μ univ).toNNReal
  rw [ENNReal.coe_toNNReal (measure_ne_top μ univ), ← hp, ENNReal.coe_toNNReal_eq_toReal,
    ← measureReal_def, ← hμ.apply_zero] at hdirac
  exact ⟨p, fun t ht => (hμ.eq_laplaceTransform ht).trans (hdirac.eq_laplaceTransform ht).symm⟩

/-- **The extreme rays of the completely monotone cone are exactly the exponential rays.** A
function `f` that is continuous on `[0, ∞)` and completely monotone on `(0, ∞)` satisfies the
decomposition condition (whenever `f = g + h` on `[0, ∞)` with `g` and `h` of the same kind, `g`
is a scalar multiple of `f` on `[0, ∞)`) if and only if `f t = f 0 * exp (-(t * p))` for all
`t ≥ 0`, for some rate `p ≥ 0`. -/
theorem extreme_ray_iff_exists_eq_mul_exp_neg_mul (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    (∀ g h : ℝ → ℝ, IsContinuousCompletelyMonotoneOnIoi g →
      IsContinuousCompletelyMonotoneOnIoi h → (∀ t : ℝ, 0 ≤ t → g t + h t = f t) →
        ∃ a : ℝ, ∀ t : ℝ, 0 ≤ t → g t = a * f t) ↔
      ∃ p : ℝ≥0, ∀ t : ℝ, 0 ≤ t → f t = f 0 * Real.exp (-(t * (p : ℝ))) := by
  refine ⟨hf.exists_eq_mul_exp_neg_mul_of_extreme_ray, ?_⟩
  rintro ⟨p, hp⟩ g h hg hh hgh
  rcases hf.nonneg_zero.eq_or_lt with hf0 | hf0
  · -- If `f 0 = 0` then `f` vanishes on `[0, ∞)`, and so do its nonnegative summands.
    refine ⟨0, fun t ht => ?_⟩
    have hft : f t = 0 := by rw [hp t ht, ← hf0, zero_mul]
    linarith [hgh t ht, hg.nonneg ht, hh.nonneg ht]
  · -- Otherwise rescale to a decomposition of the unit exponential `exp (-(t * p))`.
    have hc : 0 ≤ (f 0)⁻¹ := inv_nonneg.mpr hf0.le
    obtain ⟨a, -, -, ha, -⟩ := NNReal.exp_neg_mul_extreme_ray p (hg.smul hc) (hh.smul hc)
      fun t ht => by
        simp only [Pi.smul_apply, smul_eq_mul, ← mul_add, hgh t ht, hp t ht]
        field_simp
    refine ⟨a, fun t ht => ?_⟩
    have hat := ha t ht
    simp only [Pi.smul_apply, smul_eq_mul] at hat
    rw [hp t ht, ← mul_inv_cancel_left₀ hf0.ne' (g t), hat]
    ring

end IsContinuousCompletelyMonotoneOnIoi

end TauCeti
