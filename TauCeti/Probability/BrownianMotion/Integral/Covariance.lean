/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Elementary
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Independence.Filtration
import Mathlib.Probability.Independence.Integration

/-!
# Covariance of elementary Brownian integrals

Weighted increments on overlapping intervals have inner product equal to the expected
product of their predictable heights times the length of the intersection. Unlike the
disjoint-interval isometry, this identity compares different elementary presentations
without first choosing a common grid. It supplies the Gram identity for completion of
random predictable integrands in the time-product L² space.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {ξ η : Ω → ℝ}
  {s t u v : ℝ≥0}

private theorem integral_mul_sub_mul_sub_same_start
    (hW : IsFilteredPreBrownianReal ℱ W P) (hut : u ≤ t) (huv : u ≤ v)
    {ζ : Ω → ℝ} (hζ : StronglyMeasurable[ℱ u] ζ) :
    ∫ ω, ζ ω * ((W t ω - W u ω) * (W v ω - W u ω)) ∂P =
      (∫ ω, ζ ω ∂P) * ((min t v : ℝ≥0) - u : ℝ) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hind : IndepFun ζ (fun ω ↦ (W t ω - W u ω) * (W v ω - W u ω)) P := by
    have hi : IndepFun (fun ω (r : Set.Ici u) ↦ W r ω - W u ω) ζ P :=
      indep_of_indep_of_le_right (hW.adapted.indep_comap_sub_Ici hW.indep_sub u)
        hζ.measurable.comap_le
    exact (hi.comp ((measurable_pi_apply ⟨t, hut⟩).mul
      (measurable_pi_apply ⟨v, huv⟩)) measurable_id).symm
  rw [hind.integral_fun_mul_eq_mul_integral
    (hζ.mono (ℱ.le u)).aestronglyMeasurable
    ((hW.adapted.measurable.sub hW.adapted.measurable).mul
      (hW.adapted.measurable.sub hW.adapted.measurable)).aestronglyMeasurable]
  congr 1
  have hmean (a b : ℝ≥0) : ∫ ω, W a ω - W b ω ∂P = 0 := by
    rw [integral_sub (hW.toIsPreBrownianReal.integrable_eval a)
      (hW.toIsPreBrownianReal.integrable_eval b),
      hW.toIsPreBrownianReal.integral_eval, hW.toIsPreBrownianReal.integral_eval, sub_self]
  have hcov := covariance_fun_sub_fun_sub (hW.toIsPreBrownianReal.memLp_eval t (by norm_num))
    (hW.toIsPreBrownianReal.memLp_eval u (by norm_num))
    (hW.toIsPreBrownianReal.memLp_eval v (by norm_num))
    (hW.toIsPreBrownianReal.memLp_eval u (by norm_num))
  simp only [hW.toIsPreBrownianReal.covariance_eval, min_eq_right hut,
    min_eq_left huv, min_self, sub_add_cancel] at hcov
  simpa only [covariance, hmean, sub_zero] using hcov

private theorem integral_mul_sub_mul_mul_sub_of_le
    (hW : IsFilteredPreBrownianReal ℱ W P) (hst : s ≤ t) (huv : u ≤ v) (hsu : s ≤ u)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hη : StronglyMeasurable[ℱ u] η)
    (hξ₂ : MemLp ξ 2 P) (hη₂ : MemLp η 2 P) :
    ∫ ω, (ξ ω * (W t ω - W s ω)) * (η ω * (W v ω - W u ω)) ∂P =
      (∫ ω, ξ ω * η ω ∂P) * (↑(min t v - max s u) : ℝ) := by
  by_cases htu : t ≤ u
  · rw [hW.integral_mul_sub_mul_mul_sub_eq_zero hst htu huv hξ hη]
    simp [max_eq_right hsu, tsub_eq_zero_of_le ((min_le_left t v).trans htu)]
  · have hut : u ≤ t := (lt_of_not_ge htu).le
    have hξu := hξ.mono (ℱ.mono hsu)
    have hearly := hW.integral_mul_sub_mul_mul_sub_eq_zero hsu le_rfl huv hξ hη
    have hcross := hW.integral_mul_sub_mul_sub_same_start hut huv (hξu.mul hη)
    have hi₁ : Integrable (fun ω ↦
        (ξ ω * (W u ω - W s ω)) * (η ω * (W v ω - W u ω))) P :=
      (hW.memLp_mul_sub hsu hξ hξ₂).integrable_mul (hW.memLp_mul_sub huv hη hη₂)
    have hi₂ : Integrable (fun ω ↦
        (ξ ω * (W t ω - W u ω)) * (η ω * (W v ω - W u ω))) P :=
      (hW.memLp_mul_sub hut hξu hξ₂).integrable_mul (hW.memLp_mul_sub huv hη hη₂)
    have hexpand (ω : Ω) : (ξ ω * (W t ω - W s ω)) * (η ω * (W v ω - W u ω)) =
        (ξ ω * (W u ω - W s ω)) * (η ω * (W v ω - W u ω)) +
          (ξ ω * (W t ω - W u ω)) * (η ω * (W v ω - W u ω)) := by ring
    simp_rw [hexpand]
    rw [integral_add hi₁ hi₂, hearly, zero_add]
    simpa only [max_eq_right hsu, NNReal.coe_sub (le_min hut huv), Pi.mul_apply,
      mul_assoc, mul_left_comm, mul_comm] using hcross

/-- The cross-isometry for two elementary Brownian increments, including overlapping or
nested intervals. Heights need only be square integrable and known at their own left
endpoints; their mutual independence is not required. -/
theorem integral_mul_sub_mul_mul_sub (hW : IsFilteredPreBrownianReal ℱ W P)
    (hst : s ≤ t) (huv : u ≤ v)
    (hξ : StronglyMeasurable[ℱ s] ξ) (hη : StronglyMeasurable[ℱ u] η)
    (hξ₂ : MemLp ξ 2 P) (hη₂ : MemLp η 2 P) :
    ∫ ω, (ξ ω * (W t ω - W s ω)) * (η ω * (W v ω - W u ω)) ∂P =
      (∫ ω, ξ ω * η ω ∂P) * (↑(min t v - max s u) : ℝ) := by
  rcases le_total s u with hsu | hus
  · exact hW.integral_mul_sub_mul_mul_sub_of_le hst huv hsu hξ hη hξ₂ hη₂
  · simpa only [mul_comm, min_comm, max_comm] using
      hW.integral_mul_sub_mul_mul_sub_of_le huv hst hus hη hξ hη₂ hξ₂

end TauCeti.Probability.IsFilteredPreBrownianReal
