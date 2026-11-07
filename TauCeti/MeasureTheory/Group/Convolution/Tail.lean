/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Group.Convolution.Power
public import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
public import TauCeti.MeasureTheory.Measure.Interval
import TauCeti.MeasureTheory.Integral.Bind
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Power-law tails of convolutions

`tendsto_rpow_mul_conv_real_Ioi_of_tendsto` adds finite power-law right-tail constants under
convolution, weighted by the other factor's total mass. No assumption on the left tails or
existence of moments is needed. The proof separates a single large summand from the event that
both summands are moderately large.

`tendsto_rpow_mul_bind_convolutionPower_real_Ioi` gives the corresponding random-sum formula: a
finite count moment of order `α + 1` suffices to multiply the tail constant by the mean count.
-/

public section

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology NNReal ENNReal MeasureTheory

namespace MeasureTheory.Measure

variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Splitting the threshold between the two summands bounds a convolution tail by the
sum of the corresponding marginal tails, weighted by the other total masses. -/
theorem conv_real_Ioi_add_le (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b : ℝ) :
    (μ ∗ ν).real (Ioi (a + b)) ≤
      μ.real (Ioi a) * ν.real univ + μ.real univ * ν.real (Ioi b) := by
  rw [conv, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  calc
    _ ≤ (μ.prod ν).real ((Ioi a ×ˢ univ) ∪ (univ ×ˢ Ioi b)) := by
      refine measureReal_mono ?_
      rintro ⟨x, y⟩ hxy
      simp only [mem_preimage, mem_Ioi] at hxy
      simp only [mem_union, mem_prod, mem_Ioi, mem_univ, and_true, true_and]
      exact lt_or_lt_of_add_lt_add hxy
    _ ≤ _ := by
      simpa using (measureReal_union_le (μ := μ.prod ν)
        (Ioi a ×ˢ univ) (univ ×ˢ Ioi b))

/-- An upper tail of a sum is covered by two large-coordinate events and the event that
both coordinates are moderately large. -/
theorem conv_real_Ioi_le (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ x : ℝ) :
    (μ ∗ ν).real (Ioi x) ≤
      μ.real (Ioi ((1 - δ) * x)) * ν.real univ +
        μ.real univ * ν.real (Ioi ((1 - δ) * x)) +
        μ.real (Ioi (δ * x)) * ν.real (Ioi (δ * x)) := by
  rw [conv, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  calc
    _ ≤ (μ.prod ν).real
        (((Ioi ((1 - δ) * x) ×ˢ univ) ∪ (univ ×ˢ Ioi ((1 - δ) * x))) ∪
          (Ioi (δ * x) ×ˢ Ioi (δ * x))) := by
      refine measureReal_mono ?_
      rintro ⟨a, b⟩ hab
      simp only [mem_preimage, mem_Ioi] at hab
      simp only [mem_union, mem_prod, mem_Ioi, mem_univ, and_true, true_and]
      by_cases ha : (1 - δ) * x < a
      · exact Or.inl (Or.inl ha)
      by_cases hb : (1 - δ) * x < b
      · exact Or.inl (Or.inr hb)
      exact Or.inr ⟨by nlinarith, by nlinarith⟩
    _ ≤ _ := by
      calc
        _ ≤ (μ.prod ν).real ((Ioi ((1 - δ) * x) ×ˢ univ) ∪
              (univ ×ˢ Ioi ((1 - δ) * x))) +
            (μ.prod ν).real (Ioi (δ * x) ×ˢ Ioi (δ * x)) := measureReal_union_le _ _
        _ ≤ _ := by
          grw [measureReal_union_le]
          simp

/-- Disjoint events with one large summand and one bounded summand give a lower bound
for the tail of a convolution. -/
theorem le_conv_real_Ioi (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ x : ℝ} (hx : 0 < x) :
    μ.real (Ioi ((1 + δ) * x)) * ν.real (Icc (-(δ * x)) (δ * x)) +
        μ.real (Icc (-(δ * x)) (δ * x)) * ν.real (Ioi ((1 + δ) * x)) ≤
      (μ ∗ ν).real (Ioi x) := by
  rw [conv, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  rw [← measureReal_prod_prod, ← measureReal_prod_prod, ← measureReal_union]
  · refine measureReal_mono ?_
    rintro ⟨a, b⟩ (hab | hab) <;> simp only [mem_prod, mem_Ioi, mem_Icc] at hab
    · simp only [mem_preimage, mem_Ioi]
      nlinarith [hab.1, hab.2.1]
    · simp only [mem_preimage, mem_Ioi]
      nlinarith [hab.1.1, hab.2]
  · rw [Set.disjoint_left]
    rintro ⟨a, b⟩ hab hba
    simp only [mem_prod, mem_Ioi, mem_Icc] at hab hba
    nlinarith [hab.1, hba.1.2]
  · exact measurableSet_Icc.prod measurableSet_Ioi

/-- Finite measures with power-law right tails retain that exponent under convolution;
the constants add with the total masses of the other factors. This includes zero constants
and requires no left-tail or moment hypotheses. -/
theorem tendsto_rpow_mul_conv_real_Ioi_of_tendsto {α C D : ℝ} (hα : 0 < α)
    (hμ : Tendsto (fun x : ℝ ↦ x ^ α * μ.real (Ioi x)) atTop (𝓝 C))
    (hν : Tendsto (fun x : ℝ ↦ x ^ α * ν.real (Ioi x)) atTop (𝓝 D)) :
    Tendsto (fun x : ℝ ↦ x ^ α * (μ ∗ ν).real (Ioi x)) atTop
      (𝓝 (C * ν.real univ + μ.real univ * D)) := by
  -- Fixed relative windows exhaust the real line and recover both single-large-jump terms.
  have lower {δ : ℝ} (hδ : 0 < δ) :
      Tendsto (fun x : ℝ ↦
        (x ^ α * μ.real (Ioi ((1 + δ) * x))) * ν.real (Icc (-(δ * x)) (δ * x)) +
        μ.real (Icc (-(δ * x)) (δ * x)) * (x ^ α * ν.real (Ioi ((1 + δ) * x))))
        atTop (𝓝 ((1 + δ) ^ (-α) * (C * ν.real univ + μ.real univ * D))) := by
    convert ((hμ.rpow_mul_comp_const_mul (by linarith : 0 < 1 + δ)).mul
      (ν.tendsto_measureReal_Icc_neg_mul_atTop hδ)).add
      ((μ.tendsto_measureReal_Icc_neg_mul_atTop hδ).mul
        (hν.rpow_mul_comp_const_mul (by linarith : 0 < 1 + δ))) using 2
    rw [Real.rpow_neg (by linarith : 0 ≤ 1 + δ)]
    ring
  -- The simultaneous moderate-jump term vanishes after multiplication by the tail power.
  have upper {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
      Tendsto (fun x : ℝ ↦
        (x ^ α * μ.real (Ioi ((1 - δ) * x))) * ν.real univ +
          μ.real univ * (x ^ α * ν.real (Ioi ((1 - δ) * x))) +
          (x ^ α * μ.real (Ioi (δ * x))) * ν.real (Ioi (δ * x)))
        atTop (𝓝 ((1 - δ) ^ (-α) * (C * ν.real univ + μ.real univ * D))) := by
    have htail := (hν.rpow_mul_comp_const_mul hδ).of_rpow_mul hα
    convert (((hμ.rpow_mul_comp_const_mul (by linarith : 0 < 1 - δ)).mul_const (ν.real univ)).add
      ((hν.rpow_mul_comp_const_mul (by linarith : 0 < 1 - δ)).const_mul (μ.real univ))).add
      ((hμ.rpow_mul_comp_const_mul hδ).mul htail) using 2
    rw [Real.rpow_neg (by linarith : 0 ≤ 1 - δ)]
    ring
  -- Finally shrink the relative window to squeeze the upper and lower constants together.
  have near (sgn : ℝ) : Tendsto
      (fun δ : ℝ ↦ (1 + sgn * δ) ^ (-α) * (C * ν.real univ + μ.real univ * D))
      (𝓝[>] 0) (𝓝 (C * ν.real univ + μ.real univ * D)) := by
    have h : ContinuousAt
        (fun δ : ℝ ↦ (1 + sgn * δ) ^ (-α) * (C * ν.real univ + μ.real univ * D)) 0 := by
      fun_prop (disch := norm_num)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨δ, hδ, haδ⟩ :=
      (hpos.and ((near 1).eventually (eventually_gt_nhds ha))).exists
    simp only [one_mul] at haδ
    filter_upwards [(lower hδ).eventually (eventually_gt_nhds haδ),
      eventually_gt_atTop 0] with x hax hx
    apply hax.trans_le
    convert mul_le_mul_of_nonneg_left (le_conv_real_Ioi μ ν (δ := δ) hx)
      (Real.rpow_nonneg hx.le α) using 1; ring
  · intro a ha
    obtain ⟨δ, hδ, hδ', hδa⟩ :=
      (hpos.and (hsmall.and ((near (-1)).eventually (eventually_lt_nhds ha)))).exists
    simp only [neg_one_mul, ← sub_eq_add_neg] at hδa
    filter_upwards [(upper hδ hδ').eventually (eventually_lt_nhds hδa),
      eventually_gt_atTop 0] with x hxa hx
    apply lt_of_le_of_lt _ hxa
    convert mul_le_mul_of_nonneg_left (conv_real_Ioi_le μ ν δ x)
      (Real.rpow_nonneg hx.le α) using 1; ring

/-- A union bound for a finite convolution power, with equal shares of the threshold. -/
theorem convolutionPower_real_Ioi_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (μ.convolutionPower n).real (Ioi x) ≤ (n : ℝ) * μ.real (Ioi (x / n)) := by
  induction n, hn using Nat.le_induction generalizing x with
  | base => simp
  | succ n hn ih =>
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hsplit : x = (n : ℝ) * (x / (n + 1)) + x / (n + 1) := by
      field_simp
    rw [convolutionPower_succ]
    calc
      _ ≤ (μ.convolutionPower n).real (Ioi ((n : ℝ) * (x / (n + 1)))) +
          μ.real (Ioi (x / (n + 1))) := by
        simpa only [← hsplit, probReal_univ, mul_one, one_mul] using
          conv_real_Ioi_add_le (μ.convolutionPower n) μ
            ((n : ℝ) * (x / (n + 1))) (x / (n + 1))
      _ ≤ (n : ℝ) * μ.real (Ioi (x / (n + 1))) + μ.real (Ioi (x / (n + 1))) := by
        gcongr
        simpa only [mul_div_cancel_left₀ _ hn0] using ih ((n : ℝ) * (x / (n + 1)))
      _ = _ := by push_cast; ring

/-- The power-law right-tail constant of an `n`-fold convolution of a probability law is
`n` times the original constant, including the empty convolution. -/
theorem tendsto_rpow_mul_convolutionPower_real_Ioi {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {α C : ℝ} (hα : 0 < α)
    (hμ : Tendsto (fun x : ℝ ↦ x ^ α * μ.real (Ioi x)) atTop (𝓝 C)) (n : ℕ) :
    Tendsto (fun x : ℝ ↦ x ^ α * (μ.convolutionPower n).real (Ioi x)) atTop
      (𝓝 ((n : ℝ) * C)) := by
  induction n with
  | zero =>
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with x hx
    simp [measureReal_def, hx.le]
  | succ n ih =>
    simpa only [convolutionPower_succ, probReal_univ, mul_one, one_mul,
      Nat.cast_add_one, add_mul] using tendsto_rpow_mul_conv_real_Ioi_of_tendsto hα ih hμ

/-- A uniform normalized tail bound for a probability law gives a polynomial bound of order
`α + 1` for its convolution powers, including the empty convolution. -/
theorem rpow_mul_convolutionPower_real_Ioi_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {α K : ℝ} (hα : 0 ≤ α)
    (hμ : ∀ x : ℝ, 0 < x → x ^ α * μ.real (Ioi x) ≤ K) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ α * (μ.convolutionPower n).real (Ioi x) ≤ K * (n : ℝ) ^ (α + 1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [measureReal_def, hx.le, zero_rpow (by positivity : α + 1 ≠ 0)]
  · have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    calc
      _ ≤ x ^ α * ((n : ℝ) * μ.real (Ioi (x / n))) :=
        mul_le_mul_of_nonneg_left (convolutionPower_real_Ioi_le μ hn x)
          (rpow_nonneg hx.le α)
      _ = (n : ℝ) ^ (α + 1) * ((x / n) ^ α * μ.real (Ioi (x / n))) := by
        rw [rpow_add hn', rpow_one, div_rpow hx.le hn'.le]
        field_simp [(rpow_pos_of_pos hn' α).ne']
      _ ≤ (n : ℝ) ^ (α + 1) * K := mul_le_mul_of_nonneg_left
        (hμ _ (div_pos hx hn')) (rpow_nonneg hn'.le _)
      _ = _ := mul_comm _ _

/-- Mixing convolution powers against a count law with a finite moment of order `α + 1`
multiplies a power-law tail constant by the mean count. Jumps may have either sign, and
their left tail is unrestricted. The count measure need not be finite. -/
theorem tendsto_rpow_mul_bind_convolutionPower_real_Ioi {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {ρ : Measure ℕ} {α C : ℝ} (hα : 0 < α)
    (hμ : Tendsto (fun x : ℝ ↦ x ^ α * μ.real (Ioi x)) atTop (𝓝 C))
    (hρ : Integrable (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) ρ) :
    Tendsto (fun x : ℝ ↦ x ^ α * (ρ.bind μ.convolutionPower).real (Ioi x)) atTop
      (𝓝 ((∫ n : ℕ, (n : ℝ) ∂ρ) * C)) := by
  obtain ⟨K, hbound⟩ := μ.exists_rpow_mul_real_Ioi_le hα.le hμ
  -- The count moment dominates the normalized finite-sum tails, so their limits can be mixed.
  have h := tendsto_integral_filter_of_dominated_convergence (μ := ρ)
    (F := fun x : ℝ ↦ fun n : ℕ ↦ x ^ α * (μ.convolutionPower n).real (Ioi x))
    (f := fun n : ℕ ↦ (n : ℝ) * C) (fun n : ℕ ↦ K * (n : ℝ) ^ (α + 1))
    (Eventually.of_forall fun _ ↦ Measurable.of_discrete.aestronglyMeasurable)
    (by
      filter_upwards [eventually_gt_atTop 0] with x hx
      exact ae_of_all _ fun n ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (rpow_nonneg hx.le _) measureReal_nonneg)]
        exact μ.rpow_mul_convolutionPower_real_Ioi_le hα.le hbound hx n)
    (hρ.const_mul K)
    (ae_of_all _ fun n ↦ tendsto_rpow_mul_convolutionPower_real_Ioi hα hμ n)
  simpa only [integral_const_mul, integral_mul_const,
    bind_apply_real Measurable.of_discrete.aemeasurable measurableSet_Ioi
      (ae_of_all _ fun _ ↦ measure_ne_top _ _)] using h

end MeasureTheory.Measure
