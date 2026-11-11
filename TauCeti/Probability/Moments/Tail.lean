/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Group.Convolution.Tail
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Power-law tails under integrable perturbations

An integrable absolute moment of positive order `α` makes the corresponding normalized tail
vanish. Consequently, adding a random variable with that moment preserves any finite limit of
`x ^ α * μ.real {ω | x < X ω}`, without an independence assumption. Reflection gives the
left-tail version. The convolution corollaries express the same fact for measures on the real
line.

These estimates transfer power-law tail constants from a large-jump component to its sum with a
remainder having sufficiently many moments. In particular, a finite second moment suffices for
every tail exponent strictly between zero and two.

The argument uses dominated convergence for the moment tail and a sandwich between thresholds
`c * x`, with `c` tending to one.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, Chapter 1 (stable tail constants and large-jump decompositions).
-/

public section

open Filter MeasureTheory Real Set
open scoped Topology

namespace MeasureTheory.Integrable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The tail of an integrable real function is little-o of the reciprocal threshold.
No finiteness assumption on the underlying measure is needed. -/
theorem tendsto_mul_measureReal_gt {f : Ω → ℝ} (hf : Integrable f μ) :
    Tendsto (fun t : ℝ ↦ t * μ.real {ω | t < f ω}) atTop (𝓝 0) := by
  have hs (t : ℝ) : NullMeasurableSet {ω | t < f ω} μ :=
    hf.aemeasurable.nullMeasurable measurableSet_Ioi
  have ht := tendsto_integral_filter_of_dominated_convergence
    (F := fun t : ℝ ↦ {ω | t < f ω}.indicator (fun _ ↦ t)) (f := fun _ ↦ (0 : ℝ))
    (fun ω ↦ ‖f ω‖)
    (.of_forall fun t ↦ aestronglyMeasurable_const.indicator₀ (hs t))
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact ae_of_all _ fun ω ↦ by
        by_cases hω : t < f ω
        · simp only [Set.indicator, mem_ofPred_eq, hω, ↓reduceIte,
            Real.norm_of_nonneg ht.le, Real.norm_eq_abs]
          exact hω.le.trans (le_abs_self _)
        · simp [Set.indicator, hω]) hf.norm
    (ae_of_all _ fun ω ↦ tendsto_nhds_of_eventually_eq (by
      filter_upwards [eventually_ge_atTop (f ω)] with t ht
      simp [not_lt.mpr ht]))
  simpa [integral_indicator₀ (hs _), integral_const, smul_eq_mul, mul_comm,
    measureReal_def] using ht

end MeasureTheory.Integrable

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The right tail of a sum is bounded by the right tail of its first summand and the
absolute tail of its second summand, with arbitrary real thresholds. -/
theorem measureReal_add_gt_le [IsFiniteMeasure μ] {X Y : Ω → ℝ} {x y : ℝ} :
    μ.real {ω | x + y < X ω + Y ω} ≤
      μ.real {ω | x < X ω} + μ.real {ω | y < |Y ω|} := by
  have hsub : {ω | x + y < X ω + Y ω} ⊆
      {ω | x < X ω} ∪ {ω | y < |Y ω|} := by
    intro ω (hω : x + y < X ω + Y ω)
    by_cases hY : y < |Y ω|
    · exact Or.inr hY
    · have hX : x < X ω := by linarith only [hω, le_of_not_gt hY, le_abs_self (Y ω)]
      exact Or.inl hX
  exact (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)

/-- A finite absolute moment of order `α > 0` makes the normalized absolute tail vanish,
also at every fixed positive multiple of the threshold. -/
theorem tendsto_rpow_mul_measureReal_abs_gt {Y : Ω → ℝ} {α c : ℝ} (hα : 0 < α)
    (hY : Integrable (fun ω ↦ |Y ω| ^ α) μ) (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ x ^ α * μ.real {ω | c * x < |Y ω|}) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ ↦ x ^ α * μ.real {ω | x < |Y ω|}) atTop (𝓝 0) := by
    apply (hY.tendsto_mul_measureReal_gt.comp (tendsto_rpow_atTop hα)).congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply, rpow_lt_rpow_iff hx (abs_nonneg _) hα]
  simpa only [zero_div] using ht.rpow_mul_comp_const_mul hc

/-- Adding a perturbation with a finite absolute `α`th moment preserves a finite right-tail
constant of exponent `α > 0`. The variables may be dependent, and the constant may be zero.
The base measure need only be finite. -/
theorem tendsto_rpow_mul_measureReal_add_gt [IsFiniteMeasure μ] {X Y : Ω → ℝ} {α C : ℝ}
    (hα : 0 < α) (hX : Tendsto (fun x : ℝ ↦ x ^ α * μ.real {ω | x < X ω}) atTop (𝓝 C))
    (hY : Integrable (fun ω ↦ |Y ω| ^ α) μ) :
    Tendsto (fun x : ℝ ↦ x ^ α * μ.real {ω | x < X ω + Y ω}) atTop (𝓝 C) := by
  have hC : Tendsto (fun c : ℝ ↦ C / c ^ α) (𝓝 1) (𝓝 C) := by
    have hc : ContinuousAt (fun c : ℝ ↦ C / c ^ α) 1 :=
      continuousAt_const.div (continuousAt_rpow_const (1 : ℝ) α (by simp)) (by simp)
    simpa only [one_rpow, div_one] using hc.tendsto
  apply tendsto_order.2
  constructor
  · intro a ha
    -- A threshold slightly above x bounds the perturbed tail from below, up to the error tail.
    have hcgt : ∀ᶠ c : ℝ in 𝓝[>] 1, 1 < c := self_mem_nhdsWithin
    have hbound : ∀ᶠ c : ℝ in 𝓝[>] 1, a < C / c ^ α :=
      (hC.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds ha)
    obtain ⟨c, hc, hac⟩ := (hcgt.and hbound).exists
    have hc0 : 0 < c := lt_trans zero_lt_one hc
    have he := tendsto_rpow_mul_measureReal_abs_gt hα hY (sub_pos.mpr hc)
    have hl := (hX.rpow_mul_comp_const_mul hc0).sub he
    simp only [sub_zero] at hl
    filter_upwards [hl.eventually (lt_mem_nhds hac), eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hm : μ.real {ω | c * x < X ω} ≤
        μ.real {ω | x < X ω + Y ω} + μ.real {ω | (c - 1) * x < |Y ω|} := by
      have hcx : x + (c - 1) * x = c * x := by ring
      simpa only [hcx, add_neg_cancel_right, abs_neg] using
        measureReal_add_gt_le (μ := μ) (X := fun ω ↦ X ω + Y ω) (Y := fun ω ↦ -Y ω)
          (x := x) (y := (c - 1) * x)
    have hp := mul_le_mul_of_nonneg_left hm (rpow_nonneg hx0.le α)
    exact hx.trans_le (by linarith)
  · intro b hb
    -- A threshold slightly below x bounds the perturbed tail from above.
    have hcIoo : ∀ᶠ c : ℝ in 𝓝[<] 1, c ∈ Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one
    have hbound : ∀ᶠ c : ℝ in 𝓝[<] 1, C / c ^ α < b :=
      (hC.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hb)
    obtain ⟨c, hc, hcb⟩ := (hcIoo.and hbound).exists
    have he := tendsto_rpow_mul_measureReal_abs_gt hα hY (sub_pos.mpr hc.2)
    have hu := (hX.rpow_mul_comp_const_mul hc.1).add he
    simp only [add_zero] at hu
    filter_upwards [hu.eventually (gt_mem_nhds hcb), eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hm : μ.real {ω | x < X ω + Y ω} ≤
        μ.real {ω | c * x < X ω} + μ.real {ω | (1 - c) * x < |Y ω|} := by
      have hcx : c * x + (1 - c) * x = x := by ring
      simpa only [hcx] using
        measureReal_add_gt_le (μ := μ) (X := X) (Y := Y) (x := c * x) (y := (1 - c) * x)
    have hp := mul_le_mul_of_nonneg_left hm (rpow_nonneg hx0.le α)
    exact lt_of_le_of_lt (by linarith) hx

/-- Adding a perturbation with a finite absolute `α`th moment preserves a finite left-tail
constant of exponent `α > 0`, without requiring independence. -/
theorem tendsto_rpow_mul_measureReal_add_lt_neg [IsFiniteMeasure μ] {X Y : Ω → ℝ} {α C : ℝ}
    (hα : 0 < α) (hX : Tendsto (fun x : ℝ ↦ x ^ α * μ.real {ω | X ω < -x}) atTop (𝓝 C))
    (hY : Integrable (fun ω ↦ |Y ω| ^ α) μ) :
    Tendsto (fun x : ℝ ↦ x ^ α * μ.real {ω | X ω + Y ω < -x}) atTop (𝓝 C) := by
  simpa only [← neg_add, lt_neg, neg_neg] using
    tendsto_rpow_mul_measureReal_add_gt (X := fun ω ↦ -X ω) (Y := fun ω ↦ -Y ω) hα
      (by simpa only [lt_neg, neg_neg] using hX)
      (by simpa only [abs_neg] using hY)

end TauCeti

namespace MeasureTheory.Measure

variable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {α C : ℝ}

/-- Convolution with a finite measure having a finite absolute `α`th moment multiplies a
right-tail constant by its total mass. For a probability convolution factor the constant is
unchanged. -/
theorem tendsto_rpow_mul_conv_real_Ioi (hα : 0 < α)
    (hμ : Tendsto (fun x : ℝ ↦ x ^ α * μ.real (Ioi x)) atTop (𝓝 C))
    (hν : Integrable (fun y : ℝ ↦ |y| ^ α) ν) :
    Tendsto (fun x : ℝ ↦ x ^ α * (μ ∗ ν).real (Ioi x)) atTop (𝓝 (C * ν.real univ)) := by
  have hνtail : Tendsto (fun x : ℝ ↦ x ^ α * ν.real (Ioi x)) atTop (𝓝 0) := by
    have habs := TauCeti.tendsto_rpow_mul_measureReal_abs_gt hα hν (c := 1) zero_lt_one
    simp only [one_mul] at habs
    refine squeeze_zero' ?_ ?_ habs
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact mul_nonneg (rpow_nonneg hx α) measureReal_nonneg
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono (fun y hy ↦ hy.trans_le (le_abs_self y))) (rpow_nonneg hx α)
  simpa only [mul_zero, add_zero] using tendsto_rpow_mul_conv_real_Ioi_of_tendsto hα hμ hνtail

/-- Convolution with a finite measure having a finite absolute `α`th moment multiplies a
left-tail constant by its total mass. Zero tail constants are included. -/
theorem tendsto_rpow_mul_conv_real_Iio_neg (hα : 0 < α)
    (hμ : Tendsto (fun x : ℝ ↦ x ^ α * μ.real (Iio (-x))) atTop (𝓝 C))
    (hν : Integrable (fun y : ℝ ↦ |y| ^ α) ν) :
    Tendsto (fun x : ℝ ↦ x ^ α * (μ ∗ ν).real (Iio (-x))) atTop
      (𝓝 (C * ν.real univ)) := by
  have hfst : Tendsto (fun x : ℝ ↦ x ^ α * (μ.prod ν).real {z : ℝ × ℝ | z.1 < -x})
      atTop (𝓝 (C * ν.real univ)) := by
    have heq (x : ℝ) : {z : ℝ × ℝ | z.1 < -x} = Iio (-x) ×ˢ univ := by ext; simp
    simpa only [heq, measureReal_prod_prod, ← mul_assoc] using hμ.mul_const (ν.real univ)
  have ht := TauCeti.tendsto_rpow_mul_measureReal_add_lt_neg hα hfst (hν.comp_snd μ)
  have hpre (x : ℝ) : (fun z : ℝ × ℝ ↦ z.1 + z.2) ⁻¹' Iio (-x) =
      {z : ℝ × ℝ | z.1 + z.2 < -x} := by ext; simp
  simpa only [conv, map_measureReal_apply (f := fun z : ℝ × ℝ ↦ z.1 + z.2)
    (measurable_fst.add measurable_snd) measurableSet_Iio, hpre] using ht

end MeasureTheory.Measure
