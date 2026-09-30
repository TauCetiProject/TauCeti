/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder
import TauCeti.MeasureTheory.Measure.Atom

/-!
# Extremal completely monotone functions are exponentials

The functions that are continuous on `[0, ∞)` and completely monotone on `(0, ∞)` form a convex
cone. A function `f` in this cone spans an extreme ray when every decomposition `f = g + h` inside
the cone, compared on `[0, ∞)`, has `g` a scalar multiple of `f`. This file shows that such an `f`
is `t ↦ f 0 * exp (-(t * p))` on `[0, ∞)` for some rate `p ≥ 0`: the exponentials are the only
possible extreme rays.

By the Hausdorff–Bernstein–Widder theorem `f` is the Laplace transform of its finite Bernstein
measure `μ`. Splitting `μ` along a measurable set and its complement splits `f` inside the cone,
so each restriction of `μ` is proportional to `μ`, and a finite measure on `ℝ≥0` with this
property is a point mass.

## Main declarations

* `TauCeti.IsContinuousCompletelyMonotoneOnIoi.exists_eq_mul_exp_neg_mul_of_extreme_ray`: a
  completely monotone function spanning an extreme ray is a nonnegative multiple of an exponential.

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

end IsContinuousCompletelyMonotoneOnIoi

end TauCeti
