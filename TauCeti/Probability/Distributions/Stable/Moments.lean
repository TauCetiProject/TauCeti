/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
public import Mathlib.Probability.HasLaw
import TauCeti.Probability.Distributions.Stable.LargeJumps
import TauCeti.Probability.Distributions.Stable.SmallJump.Limit
import TauCeti.Probability.Distributions.Stable.Operations
import TauCeti.Probability.Distributions.Affine
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Absolute moments of scalar stable laws

A positive-scale non-Gaussian stable law has a finite absolute moment of positive real
order `q` exactly when `q < α`. The critical exponent diverges, including at shape one and
both fully skewed boundaries. Gaussian and zero-scale laws have every positive-order moment.
The criterion is also stated for arbitrary random variables with a stable law.

The large-jump component has the sharp moment threshold. Its independent small-jump
factor has a finite second moment, which supplies every order below the non-Gaussian shape.
Conversely, Fubini applied to a finite absolute moment of the convolution gives a translated
large-jump component with that moment. Translation preserves moment finiteness, so the
large-jump obstruction persists in the full stable law.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {α β q : ℝ} {s : ℝ≥0} {m : ℝ}

/-- The standardized law inherits the exact large-jump moment threshold. -/
private theorem integrable_abs_rpow_standardStableMeasure_iff
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hq : 0 < q) :
    Integrable (fun x : ℝ ↦ |x| ^ q) (stableMeasure α β 1 0) ↔ q < α := by
  obtain ⟨μ, hμ, -⟩ := existsUnique_conv_stableCompensatedPoissonMeasure_eq hα hβ
    (by norm_num : (0 : ℝ) < 1)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ zero_lt_one
  constructor
  · intro h
    rw [← hμ] at h
    obtain ⟨x, hx⟩ := ((integrable_conv_iff (by fun_prop)).1 h).1.exists
    have hmap : Integrable (fun y : ℝ ↦ |y| ^ q)
        ((stableCompensatedPoissonMeasure α β 1).map (fun y ↦ x + 1 * y)) := by
      exact (integrable_map_measure (by fun_prop) (by fun_prop)).2
        (by simpa only [Function.comp_def, one_mul] using hx)
    have hlarge := (memLp_id_map_affine_iff (a := x) (b := 1) one_ne_zero).1
      ((memLp_id_ofReal_iff_integrable_abs_rpow hq _).2 hmap)
    exact (integrable_abs_rpow_stableCompensatedPoissonMeasure_iff hα hβ zero_lt_one hq).1
      ((memLp_id_ofReal_iff_integrable_abs_rpow hq _).1 hlarge)
  · intro hqα
    have hq_two : ENNReal.ofReal q ≤ 2 := by
      calc ENNReal.ofReal q ≤ ENNReal.ofReal 2 :=
            ENNReal.ofReal_le_ofReal (hqα.trans hα.2).le
           _ = 2 := by norm_num
    have hsmall := (memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq
      hα hβ zero_lt_one hμ).mono_exponent hq_two
    have hlarge := (memLp_id_ofReal_iff_integrable_abs_rpow hq _).2
      ((integrable_abs_rpow_stableCompensatedPoissonMeasure_iff hα hβ zero_lt_one hq).2 hqα)
    apply (memLp_id_ofReal_iff_integrable_abs_rpow hq _).1
    rw [← hμ, Measure.conv, memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
    exact (hsmall.comp_fst _).add (hlarge.comp_snd _)

/-- A valid scalar stable law has a finite positive real-order absolute moment exactly
below its shape, except that zero-scale and Gaussian laws have every such moment.
In particular, the positive-scale non-Gaussian critical exponent is not integrable. -/
@[simp]
theorem integrable_abs_rpow_stableMeasure_iff (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hq : 0 < q) :
    Integrable (fun x : ℝ ↦ |x| ^ q) (stableMeasure α β s m) ↔
      s = 0 ∨ α = 2 ∨ q < α := by
  by_cases hs : s = 0
  · subst s
    simp only [stableMeasure_zero_scale hα hβ, true_or, iff_true]
    exact integrable_dirac (by finiteness)
  by_cases htwo : α = 2
  · subst α
    simp only [stableMeasure_two hβ, true_or, or_true, iff_true]
    exact (memLp_id_ofReal_iff_integrable_abs_rpow hq _).1
      (memLp_id_gaussianReal' _ ENNReal.ofReal_ne_top)
  have hspos : 0 < (s : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hs)
  have hmap : (stableMeasure α β 1 0).map (fun x ↦ m + (s : ℝ) * x) =
      stableMeasure α β s m := by
    simpa [Real.sign_of_pos hspos] using
      (stableMeasure_map_affine (α := α) (β := β) (s := 1) (m := 0)
        (a := m) (b := (s : ℝ)) (Or.inl hspos.ne'))
  simp only [hs, htwo, false_or]
  rw [← hmap, ← memLp_id_ofReal_iff_integrable_abs_rpow hq,
    memLp_id_map_affine_iff hspos.ne', memLp_id_ofReal_iff_integrable_abs_rpow hq]
  exact integrable_abs_rpow_standardStableMeasure_iff ⟨hα.1, lt_of_le_of_ne hα.2 htwo⟩ hβ hq

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

/-- A random variable with a valid stable law has the same sharp positive-order absolute
moment criterion as that law, with Gaussian and zero-scale exceptions. -/
theorem integrable_abs_rpow_iff_stableMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {α β q : ℝ} {s : ℝ≥0} {m : ℝ}
    (hX : HasLaw X (TauCeti.Probability.stableMeasure α β s m) P)
    (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (hq : 0 < q) :
    Integrable (fun ω ↦ |X ω| ^ q) P ↔ s = 0 ∨ α = 2 ∨ q < α := by
  have h := integrable_map_measure (g := fun x : ℝ ↦ |x| ^ q) (by fun_prop) hX.aemeasurable
  rw [hX.map_eq] at h
  exact h.symm.trans (TauCeti.Probability.integrable_abs_rpow_stableMeasure_iff hα hβ hq)

end ProbabilityTheory.HasLaw
