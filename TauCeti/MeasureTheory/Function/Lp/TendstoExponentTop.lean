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
* `TauCeti.eLpNorm_exponent_top_le_of_eventually_le` — an eventual bound
  `eLpNorm f p μ ≤ M * a ^ (1 / p)` as `p → ∞` with `a ≠ ∞` gives `eLpNorm f ∞ μ ≤ M`;
* `TauCeti.tendsto_eLpNorm_atTop` — for a finite measure, the finite-exponent seminorms converge
  to `eLpNorm f ∞ μ`;
* `TauCeti.ae_norm_le_of_eventually_nnreal_eLpNorm_le` — an eventual bound
  `eLpNorm f q μ ≤ ENNReal.ofReal (M * a ^ (1 / q))` as `q → ∞` with `0 ≤ M` and `0 ≤ a` gives
  `‖f y‖ ≤ M` almost everywhere.

## References

* G. B. Folland, *Real Analysis*, 2nd ed., Wiley 1999, Chapter 6, Exercise 7: the same limit
  `‖f‖_q → ‖f‖_∞`, stated there for `f ∈ Lᵖ ∩ L^∞` with `p < ∞` rather than for a finite
  measure.
-/

public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

section ENorm

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

/-- **`L^∞` seminorm bound from eventual `Lᵖ` seminorm bounds.** If `a ≠ ∞` and
`eLpNorm f p μ ≤ M * a ^ (1 / p)` for all sufficiently large `p : ℝ≥0`, then
`eLpNorm f ∞ μ ≤ M`. -/
theorem eLpNorm_exponent_top_le_of_eventually_le {M a : ℝ≥0∞} (ha : a ≠ ∞)
    (h : ∀ᶠ p : ℝ≥0 in atTop, eLpNorm f p μ ≤ M * a ^ (1 / (p : ℝ))) :
    eLpNorm f ∞ μ ≤ M := by
  set a' := max 1 a
  have ha'0 : a' ≠ 0 := (zero_lt_one.trans_le (le_max_left 1 a)).ne'
  have ha'top : a' ≠ ∞ := max_ne_top ENNReal.one_ne_top ha
  have hlim : Tendsto (fun p : ℝ≥0 ↦ M * a' ^ (1 / (p : ℝ))) atTop (𝓝 M) := by
    simpa only [mul_one, Function.comp_def, id] using ENNReal.Tendsto.const_mul
      ((ENNReal.tendsto_rpow_one_div_atTop ha'0 ha'top).comp
        (NNReal.tendsto_coe_atTop.2 tendsto_id)) (.inl one_ne_zero)
  refine eLpNorm_exponent_top_le_liminf.trans ((liminf_le_liminf ?_).trans_eq hlim.liminf_eq)
  exact h.mono fun p hp ↦ hp.trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (le_max_right 1 a) (by positivity)))

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

end ENorm

/-- **Pointwise `L^∞` bound from eventual `L^q` seminorm bounds.** If `0 ≤ M`, `0 ≤ a`, and
`eLpNorm f q μ ≤ ENNReal.ofReal (M * a ^ (1 / q))` for all sufficiently large `q : ℝ≥0`, then
`‖f y‖ ≤ M` for `μ`-almost every `y`. -/
theorem ae_norm_le_of_eventually_nnreal_eLpNorm_le {α F : Type*} [MeasurableSpace α]
    [SeminormedAddGroup F] {μ : Measure α} {f : α → F} {M a : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a)
    (h : ∀ᶠ q : ℝ≥0 in atTop, eLpNorm f q μ ≤ ENNReal.ofReal (M * a ^ (1 / (q : ℝ)))) :
    ∀ᵐ y ∂μ, ‖f y‖ ≤ M := by
  have htop : eLpNorm f ∞ μ ≤ ENNReal.ofReal M :=
    eLpNorm_exponent_top_le_of_eventually_le (a := ENNReal.ofReal a) ENNReal.ofReal_ne_top <|
      h.mono fun q hq ↦ hq.trans_eq <| by
        rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_rpow_of_nonneg ha (by positivity)]
  have hf : AEStronglyMeasurable f μ := by
    by_contra hf
    exact ENNReal.ofReal_ne_top (top_le_iff.1 (eLpNorm_of_not_aestronglyMeasurable hf ▸ htop))
  rw [eLpNorm_exponent_top hf] at htop
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with y hy
  exact (ENNReal.ofReal_le_ofReal_iff hM).1 (by simpa only [ofReal_norm] using hy.trans htop)

end TauCeti
