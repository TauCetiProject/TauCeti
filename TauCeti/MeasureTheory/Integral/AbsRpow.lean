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
# Positivity and derivative of the integral of `|u| ^ p`

For `p ≥ 1` and `u ∈ Lᵖ(μ)` on an arbitrary measure space, the signed power
`|u| ^ (p - 2) u` belongs to the Hölder conjugate space `L^{p'}(μ)`
(`MeasureTheory.MemLp.abs_rpow_sub_two_mul`), so `|u| ^ (p - 2) u v` is integrable for every
`v ∈ Lᵖ(μ)` (`MeasureTheory.MemLp.integrable_abs_rpow_sub_two_mul_mul`).

For `p > 1` the function `s ↦ |s| ^ p` is differentiable with derivative `p |s| ^ (p - 2) s`
(`hasDerivAt_abs_rpow`). Differentiating under the integral sign gives, for `u, v ∈ Lᵖ(μ)` on any
measure space,

`d/dt ∫ |u + t v| ^ p dμ |_(t = 0) = p ∫ |u| ^ (p - 2) u v dμ`

(`MeasureTheory.MemLp.hasDerivAt_integral_abs_add_mul_rpow`), with specialization to continuous
functions on a compact space with a finite measure (`TauCeti.hasDerivAt_integral_abs_add_mul_rpow`).
This is the directional derivative of the `p`-th power of the `Lᵖ` norm at `u` in the direction
`v`, and the derivative of the denominator in the first variation of Rayleigh-type quotients
`(∫ (energy of u) dμ) / (∫ |u| ^ p dμ) ^ (2 / p)` such as the Yamabe quotient on `H¹`.

For a continuous function `u ≠ 0` on a compact space with a finite measure that is positive on
nonempty open sets, the integral `∫ |u| ^ p dμ` is positive for every `p > 0`
(`TauCeti.integral_abs_rpow_pos`).

## Main declarations

* `MeasureTheory.MemLp.abs_rpow_sub_two_mul`: if `u ∈ Lᵖ(μ)` (`p ≥ 1`), then
  `|u| ^ (p - 2) u ∈ L^{p'}(μ)` for the Hölder conjugate exponent `p'`.
* `MeasureTheory.MemLp.integrable_abs_rpow_sub_two_mul_mul`: if `u, v ∈ Lᵖ(μ)` (`p ≥ 1`), then
  `|u| ^ (p - 2) u v` is integrable.
* `MeasureTheory.MemLp.hasDerivAt_integral_abs_add_mul_rpow`: the derivative of
  `t ↦ ∫ |u + t v| ^ p dμ` at `t = 0` for `u, v ∈ Lᵖ(μ)` (`p > 1`).
* `TauCeti.integral_abs_rpow_pos`: positivity of `∫ |u| ^ p dμ` for a continuous `u ≠ 0`.
* `TauCeti.hasDerivAt_integral_abs_add_mul_rpow`: the continuous-function specialization on a
  compact space.
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
  refine memLp_iff.2 (lt_of_le_of_lt (TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one
    (q := ENNReal.ofReal p) (f := u) ENNReal.ofReal_ne_top hmeas ?_) ?_)
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [ENNReal.toReal_ofReal hp0, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    rcases eq_or_ne (u x) 0 with hx | hx
    · rw [hx, abs_zero, mul_zero]
      exact Real.rpow_nonneg (le_refl 0) _
    · rw [← Real.rpow_add_one (abs_ne_zero.2 hx), show p - 2 + 1 = p - 1 by ring]
  · rw [ENNReal.toReal_ofReal hp0]
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) hu.eLpNorm_ne_top

/-- For `p ≥ 1` and `u, v ∈ Lᵖ(μ)`, the product `|u| ^ (p - 2) u v` is integrable. -/
theorem integrable_abs_rpow_sub_two_mul_mul {u v : X → ℝ} {p : ℝ}
    (hu : MemLp u (ENNReal.ofReal p) μ) (hv : MemLp v (ENNReal.ofReal p) μ) (hp : 1 ≤ p) :
    Integrable (fun x ↦ |u x| ^ (p - 2) * u x * v x) μ := by
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.2 hp⟩
  have : (ENNReal.conjExponent (ENNReal.ofReal p)).HolderConjugate (ENNReal.ofReal p) :=
    (inferInstance : (ENNReal.ofReal p).HolderConjugate _).symm
  exact (hu.abs_rpow_sub_two_mul (q' := ENNReal.conjExponent (ENNReal.ofReal p))).integrable_mul
    hv

/-- **Differentiating `∫ |u + t v| ^ p dμ` on `Lᵖ`.** For `p > 1` and `u, v ∈ Lᵖ(μ)` on an
arbitrary measure space, the derivative of `t ↦ ∫ |u + t v| ^ p dμ` at `t = 0` is
`p ∫ |u| ^ (p - 2) u v dμ`. -/
theorem hasDerivAt_integral_abs_add_mul_rpow {u v : X → ℝ} {p : ℝ}
    (hu : MemLp u (ENNReal.ofReal p) μ) (hv : MemLp v (ENNReal.ofReal p) μ) (hp : 1 < p) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, |u x + t * v x| ^ p ∂μ)
      (p * ∫ x, |u x| ^ (p - 2) * u x * v x ∂μ) 0 := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp_ne0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.2 hp0
  have hlin (t : ℝ) : MemLp (fun x ↦ u x + t * v x) (ENNReal.ofReal p) μ := by
    simpa only [Pi.add_def, Pi.smul_def, smul_eq_mul] using hu.add (hv.const_mul t)
  have hint0 : Integrable (fun x ↦ |u x + (0 : ℝ) * v x| ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using
      (hlin 0).integrable_norm_rpow hp_ne0 ENNReal.ofReal_ne_top
  have hderiv (x : X) (t : ℝ) : HasDerivAt (fun t ↦ |u x + t * v x| ^ p)
      (p * (|u x + t * v x| ^ (p - 2) * (u x + t * v x) * v x)) t := by
    simpa only [Function.comp_def, id, one_mul, mul_assoc] using
      (hasDerivAt_abs_rpow (u x + t * v x) hp).comp t
        (((hasDerivAt_id t).mul_const (v x)).const_add (u x))
  have hbound (x : X) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) :
      ‖p * (|u x + t * v x| ^ (p - 2) * (u x + t * v x) * v x)‖ ≤
        p * ((|u x| + |v x|) ^ (p - 1) * |v x|) := by
    have ht' : |t| ≤ 1 := by simpa using (Metric.mem_ball.1 ht).le
    have htv : |t * v x| ≤ |v x| := by
      rw [abs_mul]; nlinarith [abs_nonneg (v x), abs_nonneg t]
    have hy : |u x + t * v x| ≤ |u x| + |v x| := by linarith [abs_add_le (u x) (t * v x)]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hp0,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      ← Real.rpow_add_one' (abs_nonneg _) (by linarith), show p - 2 + 1 = p - 1 by ring]
    gcongr
  have hdom : Integrable (fun x ↦ p * ((|u x| + |v x|) ^ (p - 1) * |v x|)) μ := by
    have hsum : MemLp (fun x ↦ |u x| + |v x|) (ENNReal.ofReal p) μ := by
      simpa only [Pi.add_def, Real.norm_eq_abs] using hu.norm.add hv.norm
    have hv_abs : MemLp (fun x ↦ |v x|) (ENNReal.ofReal p) μ := by
      simpa only [Real.norm_eq_abs] using hv.norm
    refine ((hsum.integrable_abs_rpow_sub_two_mul_mul hv_abs hp.le).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)).const_mul p
    dsimp only
    have hnn : 0 ≤ |u x| + |v x| := by positivity
    rw [abs_of_nonneg hnn, ← Real.rpow_add_one' hnn (by linarith),
      show p - 2 + 1 = p - 1 by ring]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F' := fun t x ↦ p * (|u x + t * v x| ^ (p - 2) * (u x + t * v x) * v x))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Filter.Eventually.of_forall fun t ↦ by
      simpa only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using
        ((hlin t).integrable_norm_rpow hp_ne0 ENNReal.ofReal_ne_top).aestronglyMeasurable)
    hint0
    (((hlin 0).integrable_abs_rpow_sub_two_mul_mul hv hp.le).const_mul p).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound) hdom
    (Filter.Eventually.of_forall fun x t _ ↦ hderiv x t)
  simpa only [zero_mul, add_zero, integral_const_mul] using h.2

end MeasureTheory.MemLp

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- The integral `∫ |u| ^ p dμ` of a continuous function `u ≠ 0` on a compact space is positive
for `p > 0`, when the finite measure `μ` is positive on nonempty open sets. -/
theorem integral_abs_rpow_pos [μ.IsOpenPosMeasure] {u : X → ℝ} (hu : Continuous u) (hu0 : u ≠ 0)
    {p : ℝ} (hp : 0 < p) :
    0 < ∫ x, |u x| ^ p ∂μ := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hu0
  exact (hu.abs.rpow_const fun _ ↦ Or.inr hp.le).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (HasCompactSupport.of_compactSpace _) (fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (Real.rpow_pos_of_pos (abs_pos.2 hx) p).ne'

/-- **Differentiating `∫ |u + t v| ^ p dμ`.** For continuous `u` and `v` on a compact space with
a finite measure and `p > 1`, the derivative of `t ↦ ∫ |u + t v| ^ p dμ` at `t = 0` is
`p ∫ |u| ^ (p - 2) u v dμ`. -/
theorem hasDerivAt_integral_abs_add_mul_rpow {u v : X → ℝ} (hu : Continuous u)
    (hv : Continuous v) {p : ℝ} (hp : 1 < p) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, |u x + t * v x| ^ p ∂μ)
      (p * ∫ x, |u x| ^ (p - 2) * u x * v x ∂μ) 0 :=
  (hu.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace u)).hasDerivAt_integral_abs_add_mul_rpow
    (hv.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace v)) hp

end TauCeti
