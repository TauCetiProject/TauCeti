/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Essential bounds from multiplier estimates

If multiplication by a function `a` increases `Lᵖ` norms by at most a factor `C`, for some
finite exponent `p`, then `a` is essentially bounded by `C`. This file proves two forms of this
multiplier criterion on a sigma-finite measure space:

* `MeasureTheory.eLpNorm_top_le_of_forall_eLpNorm_indicator_le`: it suffices to test the
  estimate on indicators of sets of finite measure, that is, to know
  `‖a 𝟙_s‖_p ≤ C μ(s) ^ (1 / p)` for all such sets `s`;
* `MeasureTheory.eLpNorm_top_le_of_dense_of_eLpNorm_mul_le`: it suffices to test the estimate
  `‖a f‖_p ≤ C ‖f‖_p` on a dense set of functions `f` in `Lᵖ`, for `1 ≤ p < ∞`.

No integrability of `a` is assumed beyond almost-everywhere strong measurability. In the second
form, an indicator is approximated in `Lᵖ` by test functions, a subsequence converges almost
everywhere, and Fatou's lemma for `Lᵖ` seminorms passes the estimate to the indicator.

A typical application is to trigonometric polynomials on the circle: a function whose
multiplication operator is bounded on trigonometric polynomials in `L²` is essentially bounded.
This identifies the operators on circle `L²` commuting with the bilateral shift as the
multiplication operators by essentially bounded symbols.
-/

public section

open Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}

/-- **Multiplier criterion, indicator form.** On a sigma-finite measure space, if for some
exponent `0 < p < ∞` every set `s` of finite measure satisfies `‖a 𝟙_s‖_p ≤ C μ(s) ^ (1 / p)`,
then `a` is essentially bounded by `C`. -/
theorem eLpNorm_top_le_of_forall_eLpNorm_indicator_le {ε : Type*} [TopologicalSpace ε]
    [ESeminormedAddMonoid ε] [SigmaFinite μ] {a : α → ε} (ha : AEStronglyMeasurable a μ)
    (hp : p ≠ 0) (hp_top : p ≠ ∞) {C : ℝ≥0∞}
    (h : ∀ s, MeasurableSet s → μ s < ∞ →
      eLpNorm (s.indicator a) p μ ≤ C * μ s ^ (1 / p.toReal)) :
    eLpNorm a ∞ μ ≤ C := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  -- Integrating `‖a‖ₑ ^ p` over each set of finite measure compares it with the constant `C ^ p`.
  have hle : (fun x ↦ ‖a x‖ₑ ^ p.toReal) ≤ᵐ[μ] fun _ ↦ C ^ p.toReal := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ (ha.enorm.pow_const _)
      fun s hs hμs ↦ ?_
    have hs' := h s hs hμs
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp_top ha.restrict] at hs'
    rw [setLIntegral_const]
    calc ∫⁻ x in s, ‖a x‖ₑ ^ p.toReal ∂μ
        = ((∫⁻ x in s, ‖a x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)) ^ p.toReal := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp_pos.ne', ENNReal.rpow_one]
      _ ≤ (C * μ s ^ (1 / p.toReal)) ^ p.toReal := by gcongr
      _ = C ^ p.toReal * μ s := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le, ← ENNReal.rpow_mul,
            one_div_mul_cancel hp_pos.ne', ENNReal.rpow_one]
  rw [eLpNorm_exponent_top ha]
  refine eLpNormEssSup_le_of_ae_enorm_bound ?_
  filter_upwards [hle] with x hx
  exact (ENNReal.rpow_le_rpow_iff hp_pos).1 hx

variable {𝕜 : Type*} [NormedRing 𝕜] [NormOneClass 𝕜]

/-- **Multiplier criterion.** On a sigma-finite measure space, if for some exponent
`1 ≤ p < ∞` multiplication by `a` satisfies `‖a f‖_p ≤ C ‖f‖_p` for all `f` in a dense subset
of `Lᵖ`, then `a` is essentially bounded by `C`. -/
theorem eLpNorm_top_le_of_dense_of_eLpNorm_mul_le [SigmaFinite μ] [Fact (1 ≤ p)]
    (hp_top : p ≠ ∞) {a : α → 𝕜} (ha : AEStronglyMeasurable a μ) {D : Set (Lp 𝕜 p μ)}
    (hD : Dense D) {C : ℝ≥0∞} (h : ∀ f ∈ D, eLpNorm (a * ⇑f) p μ ≤ C * eLpNorm f p μ) :
    eLpNorm a ∞ μ ≤ C := by
  rcases eq_or_ne C ∞ with rfl | hC
  · exact le_top
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  refine eLpNorm_top_le_of_forall_eLpNorm_indicator_le ha hp hp_top fun s hs hμs ↦ ?_
  set g := indicatorConstLp p hs hμs.ne (1 : 𝕜)
  -- Approximate the indicator `g` by test functions, along a subsequence converging a.e.
  obtain ⟨f, hfD, hfg⟩ := mem_closure_iff_seq_limit.1 (hD.closure_eq ▸ Set.mem_univ g)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' f g).1 hfg)).exists_seq_tendsto_ae
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ (a * ⇑(f (ns n))) x) atTop (𝓝 (s.indicator a x)) := by
    filter_upwards [hae, indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs.ne)
      (c := (1 : 𝕜))] with x hx hgx
    have hax : s.indicator a x = a x * g x := by
      rw [hgx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    rw [hax]
    exact hx.const_mul (a x)
  have hnorm : Tendsto (fun n ↦ C * eLpNorm (f (ns n)) p μ) atTop (𝓝 (C * eLpNorm g p μ)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr hC)
    simp_rw [← Lp.enorm_def]
    exact (continuous_enorm.tendsto g).comp (hfg.comp hns.tendsto_atTop)
  calc eLpNorm (s.indicator a) p μ
      ≤ atTop.liminf fun n ↦ eLpNorm (a * ⇑(f (ns n))) p μ :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n ↦ ha.mul (Lp.aestronglyMeasurable _)) _
          (ha.indicator hs) hlim
    _ ≤ atTop.liminf fun n ↦ C * eLpNorm (f (ns n)) p μ :=
        liminf_le_liminf (Eventually.of_forall fun n ↦ h _ (hfD _))
    _ = C * eLpNorm g p μ := hnorm.liminf_eq
    _ = C * μ s ^ (1 / p.toReal) := by
        rw [eLpNorm_congr_ae indicatorConstLp_coeFn,
          eLpNorm_indicator_const hs.nullMeasurableSet hp hp_top, enorm_one, one_mul]

end MeasureTheory
