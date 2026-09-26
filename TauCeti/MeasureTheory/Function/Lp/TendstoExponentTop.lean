/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The `L^∞` seminorm as the limit of the `Lᵖ` seminorms

For an almost everywhere strongly measurable function `f`, the essential supremum of `‖f‖ₑ` is
recovered from the finite-exponent seminorms as `p → ∞`:

* against an arbitrary measure, `eLpNorm f ∞ μ` is at most the `liminf` of `eLpNorm f p μ`, by
  Chebyshev's inequality applied on a set of positive measure where `‖f‖ₑ` is close to its
  essential supremum;
* against a finite measure, `eLpNorm f p μ` converges to `eLpNorm f ∞ μ`, the missing half being
  the comparison `eLpNorm f p μ ≤ eLpNorm f ∞ μ * μ univ ^ (1 / p)`.

The finite-measure hypothesis cannot be dropped from the convergence statement: for the constant
function `1` on `ℝ` with Lebesgue measure, every finite-exponent seminorm is `∞` while the
essential supremum is `1`.

The exponent runs over `ℝ≥0`, coerced to `ℝ≥0∞`, so that `Filter.atTop` is the limit `p → ∞`;
the endpoint `∞` itself is `MeasureTheory.eLpNorm_exponent_top`.

## Main statements

* `TauCeti.tendsto_rpow_one_div_atTop` — the roots `c ^ (1 / p)` of a finite nonzero
  `c : ℝ≥0∞` tend to `1`;
* `TauCeti.eLpNorm_exponent_top_le_liminf` — the essential supremum is at most the `liminf` of the
  finite-exponent seminorms, for every measure;
* `TauCeti.tendsto_eLpNorm_atTop` — for a finite measure, the finite-exponent seminorms converge
  to the essential supremum.

## References

* G. B. Folland, *Real Analysis*, 2nd ed., Wiley 1999, Chapter 6, Exercise 7: the same limit
  `‖f‖_q → ‖f‖_∞`, stated there for `f ∈ Lᵖ ∩ L^∞` with `p < ∞` rather than for a finite
  measure.
-/

public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

/-- The roots `c ^ (1 / p)` of a finite nonzero extended nonnegative real tend to `1` as the
exponent `p` tends to infinity. -/
theorem tendsto_rpow_one_div_atTop {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    Tendsto (fun p : ℝ≥0 ↦ c ^ (1 / (p : ℝ))) atTop (𝓝 1) := by
  have hpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hc
  have hexp : Tendsto (fun p : ℝ≥0 ↦ 1 / (p : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def, id] using
      tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.mpr tendsto_id)
  have hreal : Tendsto (fun p : ℝ≥0 ↦ c.toReal ^ (1 / (p : ℝ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.rpow_zero] using
      ((Real.continuousAt_const_rpow hpos.ne').tendsto).comp hexp
  have hofReal := (ENNReal.continuous_ofReal.tendsto 1).comp hreal
  rw [ENNReal.ofReal_one] at hofReal
  refine hofReal.congr fun p ↦ ?_
  simp only [Function.comp_apply]
  rw [← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_toReal hc]

variable {α ε : Type*} [MeasurableSpace α] [TopologicalSpace ε] [ContinuousENorm ε]
  {μ : Measure α} {f : α → ε}

/-- **The essential supremum is below the limit inferior of the `Lᵖ` seminorms.** For every
measure and every almost everywhere strongly measurable `f`, `eLpNorm f ∞ μ` is at most the
`liminf` of `eLpNorm f p μ` as `p → ∞`. No finiteness of the measure is needed. -/
theorem eLpNorm_exponent_top_le_liminf (hf : AEStronglyMeasurable f μ) :
    eLpNorm f ∞ μ ≤ liminf (fun p : ℝ≥0 ↦ eLpNorm f p μ) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  obtain ⟨s, hrs, hs⟩ := exists_between hr
  -- `‖f‖ₑ` reaches `s` on a set of positive measure, otherwise `s` bounds the essential supremum.
  set c := μ {x | s ≤ ‖f x‖ₑ}
  have hc0 : c ≠ 0 := by
    intro hc
    have hae : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ s := by
      refine (measure_eq_zero_iff_ae_notMem.mp hc).mono fun x hx ↦ ?_
      simpa only [Set.mem_ofPred_eq, not_le] using (le_of_lt (not_le.mp hx))
    exact (lt_irrefl s) (hs.trans_le (by
      rw [eLpNorm_exponent_top hf]
      exact essSup_le_of_ae_le s hae))
  -- Chebyshev: `s * min c 1 ^ (1 / p) ≤ eLpNorm f p μ` for every nonzero finite exponent.
  set c' := min c 1
  have hc'0 : c' ≠ 0 := by simp [c', hc0]
  have hc'top : c' ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right c 1)
  have hbound : ∀ p : ℝ≥0, p ≠ 0 → s * c' ^ (1 / (p : ℝ)) ≤ eLpNorm f p μ := by
    intro p hp
    have hp0 : (p : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hp
    have hppos : 0 < (p : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hp)
    have hcheb := mul_meas_ge_le_pow_eLpNorm' μ hp0 ENNReal.coe_ne_top (f := f) s
    rw [ENNReal.coe_toReal] at hcheb
    calc s * c' ^ (1 / (p : ℝ))
        = (s ^ (p : ℝ) * c') ^ (1 / (p : ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hppos.ne', ENNReal.rpow_one]
      _ ≤ (eLpNorm f p μ ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
          refine ENNReal.rpow_le_rpow ((mul_le_mul' le_rfl (min_le_left c 1)).trans hcheb) ?_
          positivity
      _ = eLpNorm f p μ := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hppos.ne', ENNReal.rpow_one]
  have hlim : Tendsto (fun p : ℝ≥0 ↦ s * c' ^ (1 / (p : ℝ))) atTop (𝓝 s) := by
    simpa only [mul_one] using
      ENNReal.Tendsto.const_mul (tendsto_rpow_one_div_atTop hc'0 hc'top) (Or.inl one_ne_zero)
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hlim.eventually (lt_mem_nhds hrs), eventually_ne_atTop 0] with p hp hp0
  exact hp.le.trans (hbound p hp0)

/-- **The `Lᵖ` seminorms converge to the essential supremum.** Against a finite measure, for every
almost everywhere strongly measurable `f`, `eLpNorm f p μ` tends to `eLpNorm f ∞ μ` as `p → ∞`. -/
theorem tendsto_eLpNorm_atTop [IsFiniteMeasure μ] (hf : AEStronglyMeasurable f μ) :
    Tendsto (fun p : ℝ≥0 ↦ eLpNorm f p μ) atTop (𝓝 (eLpNorm f ∞ μ)) := by
  rcases eq_zero_or_neZero μ with rfl | _
  · simp
  have hμ0 : μ Set.univ ≠ 0 := by simp [NeZero.ne μ]
  refine tendsto_of_le_liminf_of_limsup_le (eLpNorm_exponent_top_le_liminf hf) ?_
  -- The comparison with the essential supremum weighted by the root of the total mass.
  have hlim : Tendsto (fun p : ℝ≥0 ↦ eLpNorm f ∞ μ * μ Set.univ ^ (1 / (p : ℝ))) atTop
      (𝓝 (eLpNorm f ∞ μ)) := by
    simpa only [mul_one] using ENNReal.Tendsto.const_mul
      (tendsto_rpow_one_div_atTop hμ0 (measure_ne_top μ _)) (Or.inl one_ne_zero)
  refine (limsup_le_limsup ?_).trans_eq hlim.limsup_eq
  filter_upwards [eventually_ne_atTop 0] with p hp
  have hppos : 0 < (p : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hp)
  rw [eLpNorm_eq_eLpNorm' (ENNReal.coe_ne_zero.mpr hp) ENNReal.coe_ne_top hf, ENNReal.coe_toReal,
    eLpNorm_exponent_top hf]
  exact eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hppos

end TauCeti
