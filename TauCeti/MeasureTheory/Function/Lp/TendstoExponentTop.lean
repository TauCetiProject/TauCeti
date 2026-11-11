/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The `L^∞` seminorm as the limit of the `Lᵖ` seminorms

The `L^∞` seminorm `eLpNorm f ∞ μ` is recovered from the finite-exponent seminorms as `p → ∞`.
When `f` is almost everywhere strongly measurable, `eLpNorm f ∞ μ` is the essential supremum of
`‖f‖ₑ` (`MeasureTheory.eLpNorm_exponent_top`), so this is the classical limit `‖f‖_p → ‖f‖_∞`:

* against an arbitrary measure, `eLpNorm f ∞ μ` is at most the `liminf` of `eLpNorm f p μ`, by
  Chebyshev's inequality applied on a set of positive measure where `‖f‖ₑ` is close to its
  essential supremum;
* against a finite measure, `eLpNorm f p μ` converges to `eLpNorm f ∞ μ`, the missing half being
  the comparison `eLpNorm f p μ ≤ eLpNorm f ∞ μ * μ univ ^ (1 / p)`.

No measurability hypothesis is needed: if `f` is not almost everywhere strongly measurable, then
`eLpNorm f p μ = ∞` for every exponent `p`, including `∞`, and both statements are immediate. In
that case `eLpNorm f ∞ μ` need not agree with the essential supremum of `‖f‖ₑ`.

The finite-measure hypothesis cannot be dropped from the convergence statement: for the constant
function `1` on `ℝ` with Lebesgue measure, every finite-exponent seminorm is `∞` while the
`L^∞` seminorm is `1`.

The exponent runs over `ℝ≥0`, coerced to `ℝ≥0∞`, so that `Filter.atTop` is the limit `p → ∞`;
the endpoint `∞` itself is `MeasureTheory.eLpNorm_exponent_top`.

## Main statements

* `TauCeti.eLpNorm_exponent_top_le_liminf` — `eLpNorm f ∞ μ` is at most the `liminf` of the
  finite-exponent seminorms, for every measure;
* `TauCeti.tendsto_eLpNorm_atTop` — for a finite measure, the finite-exponent seminorms converge
  to `eLpNorm f ∞ μ`.

## References

* G. B. Folland, *Real Analysis*, 2nd ed., Wiley 1999, Chapter 6, Exercise 7: the same limit
  `‖f‖_q → ‖f‖_∞`, stated there for `f ∈ Lᵖ ∩ L^∞` with `p < ∞` rather than for a finite
  measure.
-/

public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {α ε : Type*} [MeasurableSpace α] [TopologicalSpace ε] [ContinuousENorm ε]
  {μ : Measure α} {f : α → ε}

/-- **The `L^∞` seminorm is below the limit inferior of the `Lᵖ` seminorms.** For every measure
and every `f`, `eLpNorm f ∞ μ` is at most the `liminf` of `eLpNorm f p μ` as `p → ∞`. No
finiteness of the measure is needed. For almost everywhere strongly measurable `f`, the left side
is the essential supremum of `‖f‖ₑ`. -/
theorem eLpNorm_exponent_top_le_liminf :
    eLpNorm f ∞ μ ≤ liminf (fun p : ℝ≥0 ↦ eLpNorm f p μ) atTop := by
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hf]
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  obtain ⟨s, hrs, hs⟩ := exists_between hr
  -- `‖f‖ₑ` reaches `s` on a set of positive measure, otherwise `s` bounds the essential supremum.
  set c := μ {x | s ≤ ‖f x‖ₑ}
  have hc0 : c ≠ 0 := fun hc ↦ hs.not_ge <| by
    rw [eLpNorm_exponent_top hf]
    exact essSup_le_of_ae_le s <| (ae_iff.2 (by simpa only [not_lt] using hc)).mono
      fun _ ↦ le_of_lt
  -- Chebyshev gives `s * min c 1 ^ (1 / p) ≤ eLpNorm f p μ`, and the left side tends to `s`.
  set c' := min c 1
  have hc'0 : c' ≠ 0 := by simp [c', hc0]
  have hc'top : c' ≠ ∞ := by simp [c']
  have hlim : Tendsto (fun p : ℝ≥0 ↦ s * c' ^ (1 / (p : ℝ))) atTop (𝓝 s) := by
    simpa only [mul_one, Function.comp_def, id] using ENNReal.Tendsto.const_mul
      ((ENNReal.tendsto_rpow_one_div_atTop hc'0 hc'top).comp
        (NNReal.tendsto_coe_atTop.2 tendsto_id)) (.inl one_ne_zero)
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hlim.eventually (lt_mem_nhds hrs), eventually_ne_atTop 0] with p hp hp0
  refine hp.le.trans ?_
  have hppos : 0 < (p : ℝ) := by positivity
  have hcheb := mul_meas_ge_le_pow_eLpNorm' μ (ENNReal.coe_ne_zero.2 hp0) ENNReal.coe_ne_top
    (f := f) s
  rw [ENNReal.coe_toReal] at hcheb
  rw [← ENNReal.rpow_le_rpow_iff hppos, ENNReal.mul_rpow_of_nonneg _ _ hppos.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hppos.ne', ENNReal.rpow_one]
  exact (mul_le_mul' le_rfl (min_le_left c 1)).trans hcheb

/-- **The `Lᵖ` seminorms converge to the `L^∞` seminorm.** Against a finite measure, for every
`f`, `eLpNorm f p μ` tends to `eLpNorm f ∞ μ` as `p → ∞`. For almost everywhere strongly
measurable `f`, the limit is the essential supremum of `‖f‖ₑ`. -/
theorem tendsto_eLpNorm_atTop [IsFiniteMeasure μ] :
    Tendsto (fun p : ℝ≥0 ↦ eLpNorm f p μ) atTop (𝓝 (eLpNorm f ∞ μ)) := by
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · simp [eLpNorm_of_not_aestronglyMeasurable hf]
  rcases eq_zero_or_neZero μ with rfl | _
  · simp
  refine tendsto_of_le_liminf_of_limsup_le eLpNorm_exponent_top_le_liminf ?_
  -- The comparison with the `L^∞` seminorm weighted by the root of the total mass.
  have hlim : Tendsto (fun p : ℝ≥0 ↦ eLpNorm f ∞ μ * μ Set.univ ^ (1 / (p : ℝ))) atTop
      (𝓝 (eLpNorm f ∞ μ)) := by
    simpa only [mul_one, Function.comp_def, id] using ENNReal.Tendsto.const_mul
      ((ENNReal.tendsto_rpow_one_div_atTop (by simp [NeZero.ne μ]) (measure_ne_top μ _)).comp
        (NNReal.tendsto_coe_atTop.2 tendsto_id)) (.inl one_ne_zero)
  refine (limsup_le_limsup (.of_forall fun p ↦ ?_)).trans_eq hlim.limsup_eq
  simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ (le_top : (p : ℝ≥0∞) ≤ ∞) hf

end TauCeti
