/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Positivity, derivative and exponent dependence of the integral of `|u| ^ p`

For `p ≥ 1` and `u ∈ Lᵖ(μ)` on any measure space, the signed power `|u| ^ (p - 2) u` belongs to the
Hölder conjugate space `L^{p'}(μ)` (`MeasureTheory.MemLp.abs_rpow_sub_two_mul`), so
`|u| ^ (p - 2) u v` is integrable for every `v ∈ Lᵖ(μ)`
(`MeasureTheory.MemLp.integrable_abs_rpow_sub_two_mul_mul`).

For `p > 1` and `u, v ∈ Lᵖ(μ)`, differentiating under the integral sign gives
`d/dt ∫ |u + t v| ^ p dμ |_(t = 0) = p ∫ |u| ^ (p - 2) u v dμ`
(`MeasureTheory.MemLp.hasDerivAt_integral_abs_add_mul_rpow`), with continuous-function
specialization `TauCeti.hasDerivAt_integral_abs_add_mul_rpow` on a compact space. For continuous
`u ≠ 0` on a compact space with an open-positive finite measure, `∫ |u| ^ p dμ > 0` for `p > 0`
(`TauCeti.integral_abs_rpow_pos`).

On a finite measure space the moments of `u ∈ Lᵖ(μ)` are compared and vary continuously with the
exponent: for `0 < s ≤ p`, Hölder's inequality gives
`∫ |u| ^ s dμ ≤ (∫ |u| ^ p dμ) ^ (s / p) μ(X) ^ (1 - s / p)`
(`MeasureTheory.MemLp.integral_abs_rpow_le_mul_measureReal_univ_rpow`), and `s ↦ ∫ |u| ^ s dμ` is
continuous on `(0, p]` (`MeasureTheory.MemLp.continuousOn_integral_abs_rpow`).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.MemLp

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- For `p ≥ 1` and `u ∈ Lᵖ(μ)`, the signed power `|u| ^ (p - 2) u` belongs to the Hölder
conjugate space `L^{q'}(μ)`. At `p = 1` this gives essential boundedness in `L^∞(μ)`. -/
theorem abs_rpow_sub_two_mul {u : X → ℝ} {p : ℝ} {q' : ℝ≥0∞}
    (hu : MemLp u (ENNReal.ofReal p) μ) [(ENNReal.ofReal p).HolderConjugate q'] :
    MemLp (fun x ↦ |u x| ^ (p - 2) * u x) q' μ := by
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.1 (ENNReal.HolderConjugate.one_le (ENNReal.ofReal p) q')
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hmeas : AEStronglyMeasurable (fun x ↦ |u x| ^ (p - 2) * u x) μ := by
    simpa only [Pi.mul_def, Real.norm_eq_abs] using
      (hu.aestronglyMeasurable.norm.aemeasurable.pow_const
        (p - 2)).aestronglyMeasurable.mul hu.aestronglyMeasurable
  refine memLp_iff.2 ((TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one (q := ENNReal.ofReal p)
    (f := u) ENNReal.ofReal_ne_top hmeas (.of_forall fun x ↦ ?_)).trans_lt ?_)
  · rw [ENNReal.toReal_ofReal hp0, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    rcases eq_or_ne (u x) 0 with hx | hx
    · rw [hx, abs_zero, mul_zero]; positivity
    · rw [← Real.rpow_add_one (abs_ne_zero.2 hx), show p - 2 + 1 = p - 1 by ring]
  · rw [ENNReal.toReal_ofReal hp0]
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) hu.eLpNorm_ne_top

/-- For `p ≥ 1` and `u, v ∈ Lᵖ(μ)`, the product `|u| ^ (p - 2) u v` is integrable. -/
theorem integrable_abs_rpow_sub_two_mul_mul {u v : X → ℝ} {p : ℝ}
    (hu : MemLp u (ENNReal.ofReal p) μ) (hv : MemLp v (ENNReal.ofReal p) μ) (hp : 1 ≤ p) :
    Integrable (fun x ↦ |u x| ^ (p - 2) * u x * v x) μ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp⟩
  have := (inferInstance :
    (ENNReal.ofReal p).HolderConjugate (ENNReal.conjExponent (ENNReal.ofReal p))).symm
  exact (hu.abs_rpow_sub_two_mul (q' := ENNReal.conjExponent (ENNReal.ofReal p))).integrable_mul hv

/-- **Differentiating `∫ |u + t v| ^ p dμ` on `Lᵖ`.** For `p > 1` and `u, v ∈ Lᵖ(μ)` on an
arbitrary measure space, the derivative of `t ↦ ∫ |u + t v| ^ p dμ` at `t = 0` is
`p ∫ |u| ^ (p - 2) u v dμ`. -/
theorem hasDerivAt_integral_abs_add_mul_rpow {u v : X → ℝ} {p : ℝ}
    (hu : MemLp u (ENNReal.ofReal p) μ) (hv : MemLp v (ENNReal.ofReal p) μ) (hp : 1 < p) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, |u x + t * v x| ^ p ∂μ)
      (p * ∫ x, |u x| ^ (p - 2) * u x * v x ∂μ) 0 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hlin (t : ℝ) : MemLp (fun x ↦ u x + t * v x) (ENNReal.ofReal p) μ := by
    simpa only [Pi.add_def, Pi.smul_def, smul_eq_mul] using hu.add (hv.const_mul t)
  have hint (t : ℝ) : Integrable (fun x ↦ |u x + t * v x| ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using
      (hlin t).integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.2 hp0) ENNReal.ofReal_ne_top
  have hbound (x : X) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) :
      ‖p * (|u x + t * v x| ^ (p - 2) * (u x + t * v x) * v x)‖ ≤
        p * ((|u x| + |v x|) ^ (p - 1) * |v x|) := by
    have ht' : |t| ≤ 1 := by simpa using (Metric.mem_ball.1 ht).le
    have htv : |t * v x| ≤ |v x| := by rw [abs_mul]; nlinarith [abs_nonneg (v x)]
    have hy : |u x + t * v x| ≤ |u x| + |v x| := by linarith [abs_add_le (u x) (t * v x)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hp0,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      ← Real.rpow_add_one' (abs_nonneg _) (by linarith), show p - 2 + 1 = p - 1 by ring]
    gcongr
  have hdom : Integrable (fun x ↦ p * ((|u x| + |v x|) ^ (p - 1) * |v x|)) μ := by
    refine (((hu.norm.add hv.norm).integrable_abs_rpow_sub_two_mul_mul hv.norm hp.le).congr
      (.of_forall fun x ↦ ?_)).const_mul p
    dsimp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), ← Real.rpow_add_one' (by positivity) (by linarith),
      show p - 2 + 1 = p - 1 by ring]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F' := fun t x ↦ p * (|u x + t * v x| ^ (p - 2) * (u x + t * v x) * v x))
    (Metric.ball_mem_nhds 0 one_pos) (.of_forall fun t ↦ (hint t).aestronglyMeasurable) (hint 0)
    (((hlin 0).integrable_abs_rpow_sub_two_mul_mul hv hp.le).const_mul p).aestronglyMeasurable
    (.of_forall hbound) hdom (.of_forall fun x t _ ↦ by
      simpa only [Function.comp_def, id, one_mul, mul_assoc] using
        (hasDerivAt_abs_rpow (u x + t * v x) hp).comp t
          (((hasDerivAt_id t).mul_const (v x)).const_add (u x)))
  simpa only [zero_mul, add_zero, integral_const_mul] using h.2

/-- **Hölder comparison of moments on a finite measure.** For `0 < s ≤ p` and `u ∈ Lᵖ(μ)` on a
finite measure space, `∫ |u| ^ s dμ ≤ (∫ |u| ^ p dμ) ^ (s / p) μ(X) ^ (1 - s / p)`. -/
theorem integral_abs_rpow_le_mul_measureReal_univ_rpow [IsFiniteMeasure μ] {u : X → ℝ}
    {s p : ℝ} (hu : MemLp u (ENNReal.ofReal p) μ) (hs : 0 < s) (hsp : s ≤ p) :
    ∫ x, |u x| ^ s ∂μ ≤ (∫ x, |u x| ^ p ∂μ) ^ (s / p) * μ.real Set.univ ^ (1 - s / p) := by
  rcases hsp.eq_or_lt with rfl | hsp
  · rw [div_self hs.ne', sub_self, Real.rpow_zero, mul_one, Real.rpow_one]
  have hr : 1 < p / s := (one_lt_div hs).2 hsp
  have hconj := Real.HolderConjugate.conjExponent hr
  have hf : MemLp (fun x ↦ |u x| ^ s) (ENNReal.ofReal (p / s)) μ := by
    simpa only [ENNReal.toReal_ofReal hs.le, ← ENNReal.ofReal_div_of_pos hs, Real.norm_eq_abs]
      using hu.norm_rpow_div (ENNReal.ofReal s)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (.of_forall fun x ↦ Real.rpow_nonneg (abs_nonneg (u x)) s) (.of_forall fun _ ↦ zero_le_one)
    hf (memLp_const 1)
  have hpow (x : X) : (|u x| ^ s) ^ (p / s) = |u x| ^ p := by
    rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hs.ne']
  have hinv : 1 / Real.conjExponent (p / s) = 1 - s / p := by
    rw [one_div, eq_sub_iff_add_eq', ← inv_div, ← hconj.inv_add_inv_eq_one]
  simpa only [mul_one, Real.one_rpow, integral_const, smul_eq_mul, hpow, one_div_div, hinv]
    using h

/-- **Continuity of moments in the exponent.** For `u ∈ Lᵖ(μ)` on a finite measure space, the
moment `s ↦ ∫ |u| ^ s dμ` is continuous on `(0, p]`. -/
theorem continuousOn_integral_abs_rpow [IsFiniteMeasure μ] {u : X → ℝ} {p : ℝ}
    (hu : MemLp u (ENNReal.ofReal p) μ) :
    ContinuousOn (fun s ↦ ∫ x, |u x| ^ s ∂μ) (Set.Ioc 0 p) := by
  rcases le_or_gt p 0 with hp | hp
  · simp [Set.Ioc_eq_empty_of_le hp]
  have hint : Integrable (fun x ↦ |u x| ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using
      hu.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.2 hp) ENNReal.ofReal_ne_top
  refine continuousOn_of_dominated (bound := fun x ↦ 1 + |u x| ^ p)
    (fun s _ ↦ (hu.aestronglyMeasurable.norm.aemeasurable.pow_const s).aestronglyMeasurable)
    (fun s hs ↦ .of_forall fun x ↦ ?_) ((integrable_const 1).add hint)
    (.of_forall fun x s hs ↦ (Real.continuousAt_const_rpow' hs.1.ne').continuousWithinAt)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  rcases le_total |u x| 1 with hx | hx
  · linarith [Real.rpow_le_one (abs_nonneg (u x)) hx hs.1.le,
      Real.rpow_nonneg (abs_nonneg (u x)) p]
  · linarith [Real.rpow_le_rpow_of_exponent_le hx hs.2]

end MeasureTheory.MemLp

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- The integral `∫ |u| ^ p dμ` of a continuous function `u ≠ 0` on a compact space is positive
for `p > 0`, when the finite measure `μ` is positive on nonempty open sets. -/
theorem integral_abs_rpow_pos [μ.IsOpenPosMeasure] {u : X → ℝ} (hu : Continuous u) (hu0 : u ≠ 0)
    {p : ℝ} (hp : 0 < p) : 0 < ∫ x, |u x| ^ p ∂μ := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hu0
  exact (hu.abs.rpow_const fun _ ↦ Or.inr hp.le).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (.of_compactSpace _) (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (Real.rpow_pos_of_pos (abs_pos.2 hx) p).ne'

/-- **Differentiating `∫ |u + t v| ^ p dμ`.** For continuous `u` and `v` on a compact space with
a finite measure and `p > 1`, the derivative of `t ↦ ∫ |u + t v| ^ p dμ` at `t = 0` is
`p ∫ |u| ^ (p - 2) u v dμ`. -/
theorem hasDerivAt_integral_abs_add_mul_rpow {u v : X → ℝ} (hu : Continuous u)
    (hv : Continuous v) {p : ℝ} (hp : 1 < p) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, |u x + t * v x| ^ p ∂μ)
      (p * ∫ x, |u x| ^ (p - 2) * u x * v x ∂μ) 0 :=
  (hu.memLp_of_hasCompactSupport (.of_compactSpace u)).hasDerivAt_integral_abs_add_mul_rpow
    (hv.memLp_of_hasCompactSupport (.of_compactSpace v)) hp

end TauCeti
