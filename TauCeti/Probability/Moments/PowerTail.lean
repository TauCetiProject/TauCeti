/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Integral.LayerCake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Power-law tails and moment thresholds

For a nonnegative measurable function on a finite measure space, a nonzero finite limit of
`t ^ a * μ.real {x | t < f x}` determines the sharp positive moment threshold: the `p`th
moment is finite exactly when `p < a`. In particular, the critical moment diverges.

The layer-cake formula reduces this question to integrability at infinity of the weighted
tail. A finite measure controls the contribution from bounded thresholds, and comparison
with a real power decides integrability at infinity. The criterion applies to heavy-tailed
laws without any density assumption.

For real-valued functions the two tails can be supplied separately; their constants add.
One constant may vanish, as happens for fully skewed stable laws.

## Main results

* `integrable_rpow_iff_of_tendsto_weighted_tail` gives the nonnegative-function criterion.
* `integrable_abs_rpow_iff_of_tendsto_tails` gives the two-sided absolute-moment criterion.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory Real Set
open scoped ENNReal Topology

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : Ω → ℝ} {p a c : ℝ}

/-- A nonzero finite power-law tail constant determines the exact positive moment threshold,
including non-integrability at the critical exponent. No density or probability normalization
is required. -/
theorem integrable_rpow_iff_of_tendsto_weighted_tail
    (hf : AEMeasurable f μ) (hfn : 0 ≤ᵐ[μ] f) (hp : 0 < p) (hc : c ≠ 0)
    (htail : Tendsto (fun t : ℝ ↦ t ^ a * μ.real {x | t < f x}) atTop (𝓝 c)) :
    Integrable (fun x ↦ f x ^ p) μ ↔ p < a := by
  have hratio : Tendsto
      (fun t : ℝ ↦ (μ.real {x | t < f x} * t ^ (p - 1)) / t ^ (p - a - 1))
      atTop (𝓝 c) := by
    apply htail.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hexp : p - 1 - (p - a - 1) = a := by ring
    rw [mul_div_assoc, ← rpow_sub ht, hexp, mul_comm]
  have htheta := isTheta_of_div_tendsto_nhds_ne_zero hratio hc
  have hm : AEStronglyMeasurable
      (fun t : ℝ ↦ μ.real {x | t < f x} * t ^ (p - 1)) volume :=
    (measurable_weighted_tail f p).aestronglyMeasurable
  have hrm : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (p - a - 1)) volume := by fun_prop
  rw [integrable_rpow_iff_integrableAtFilter_weighted_tail hf hfn hp]
  have hequiv : IntegrableAtFilter
      (fun t : ℝ ↦ μ.real {x | t < f x} * t ^ (p - 1)) atTop ↔
        IntegrableAtFilter (fun t : ℝ ↦ t ^ (p - a - 1)) atTop :=
    ⟨fun h ↦ htheta.isBigO.integrableAtFilter hrm.stronglyMeasurableAtFilter h,
      fun h ↦ htheta.isBigO_symm.integrableAtFilter hm.stronglyMeasurableAtFilter h⟩
  rw [hequiv, integrableAtFilter_rpow_atTop_iff]
  constructor <;> intro h <;> linarith

/-- Finite power-law constants for the right and left tails determine the sharp positive
absolute-moment threshold whenever their sum is nonzero. Either individual constant may be
zero; atoms and singular measures are allowed. -/
theorem integrable_abs_rpow_iff_of_tendsto_tails
    (hf : AEMeasurable f μ) (hp : 0 < p) {cRight cLeft : ℝ} (hc : cRight + cLeft ≠ 0)
    (hplus : Tendsto (fun t : ℝ ↦ t ^ a * μ.real {x | t < f x}) atTop (𝓝 cRight))
    (hminus : Tendsto (fun t : ℝ ↦ t ^ a * μ.real {x | f x < -t}) atTop (𝓝 cLeft)) :
    Integrable (fun x ↦ |f x| ^ p) μ ↔ p < a := by
  have habs : AEMeasurable (fun x ↦ |f x|) μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  apply integrable_rpow_iff_of_tendsto_weighted_tail habs
    (ae_of_all _ fun x ↦ abs_nonneg (f x)) hp hc
  apply (hplus.add hminus).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hset : {x | t < |f x|} = {x | t < f x} ∪ {x | f x < -t} := by
    ext x
    simp only [mem_ofPred_eq, mem_union, lt_abs, lt_neg]
  have hd : Disjoint {x | t < f x} {x | f x < -t} := by
    rw [disjoint_left]
    intro x hx hx'
    simp only [mem_ofPred_eq] at hx hx'
    linarith
  rw [hset, measureReal_union₀ (nullMeasurableSet_lt hf aemeasurable_const) hd.aedisjoint,
    mul_add]

end TauCeti
