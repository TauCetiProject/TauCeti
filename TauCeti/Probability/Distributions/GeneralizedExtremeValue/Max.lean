/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Cdf
import TauCeti.Probability.Distributions.Gumbel.Max
import TauCeti.Probability.Distributions.Relations

/-!
# Maxima of generalized extreme-value variables

The maximum of a nonempty finite iid generalized extreme-value sample is again in the same
family, with the same shape. If the sample size is `n` and the shape is `ξ ≠ 0`, its scale is
`s * n ^ ξ` and its location is `m + s * (n ^ ξ - 1) / ξ`. At shape zero the scale stays `s`
and the location becomes `m + s * log n`, as for Gumbel variables.

The measure identity and its random-variable form include both signs of the shape and the
nonpositive-scale zero-measure branch. Maxima use `Finset.sup'` on a nonempty finite type.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι] {m s ξ : ℝ}

private theorem cdf_generalizedExtremeValueMeasure_max {n : ℕ} (hn : 0 < n)
    (hs : 0 < s) (hξ : ξ ≠ 0) (x : ℝ) :
    cdf (generalizedExtremeValueMeasure
        (m + s * ((n : ℝ) ^ ξ - 1) / ξ) (s * (n : ℝ) ^ ξ) ξ) x =
      cdf (generalizedExtremeValueMeasure m s ξ) x ^ n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ha : 0 < (n : ℝ) ^ ξ := Real.rpow_pos_of_pos hnR ξ
  have hsupport :
      1 + ξ * ((x - (m + s * ((n : ℝ) ^ ξ - 1) / ξ)) / (s * (n : ℝ) ^ ξ)) =
        (1 + ξ * ((x - m) / s)) / (n : ℝ) ^ ξ := by
    field_simp
    ring
  rw [cdf_generalizedExtremeValueMeasure_eq (mul_pos hs ha) hξ,
    cdf_generalizedExtremeValueMeasure_eq hs hξ, hsupport]
  simp only [div_pos_iff_of_pos_right ha]
  split_ifs with hx hshape
  · have hpower : ((n : ℝ) ^ ξ) ^ (-1 / ξ) = (n : ℝ)⁻¹ := by
      rw [← Real.rpow_mul hnR.le]
      have hexponent : ξ * (-1 / ξ) = -1 := by field_simp
      rw [hexponent, Real.rpow_neg_one]
    rw [Real.div_rpow hx.le ha.le, hpower, div_inv_eq_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  · simp [hn.ne']
  · simp

/-- The maximum of a nonempty finite iid generalized extreme-value sample is generalized
extreme-value with unchanged shape, scale multiplied by the sample size to that shape, and
the corresponding location shift. The shape-zero branch is the Gumbel logarithmic shift. -/
theorem map_max_pi_generalizedExtremeValueMeasure (m ξ : ℝ) :
    (Measure.pi fun _ : ι => generalizedExtremeValueMeasure m s ξ).map
        (fun x => Finset.univ.sup' Finset.univ_nonempty x) =
      generalizedExtremeValueMeasure
        (if ξ = 0 then m + s * Real.log (Fintype.card ι)
          else m + s * ((Fintype.card ι : ℝ) ^ ξ - 1) / ξ)
        (s * (Fintype.card ι : ℝ) ^ ξ) ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    rw [ite_eq_left rfl]
    simpa only [generalizedExtremeValueMeasure_zero, Real.rpow_zero, mul_one]
      using map_max_pi_gumbelMeasure (ι := ι) (s := s) m
  rw [ite_eq_right hξ]
  have ha : 0 < (Fintype.card ι : ℝ) ^ ξ :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr Fintype.card_pos) ξ
  rcases le_or_gt s 0 with hs | hs
  · have hpi : (Measure.pi fun _ : ι => generalizedExtremeValueMeasure m s ξ) = 0 := by
      simp_rw [generalizedExtremeValueMeasure_of_nonpos hs]
      exact Measure.measure_univ_eq_zero.mp (by simp [Measure.pi_univ])
    rw [hpi, Measure.map_zero,
      generalizedExtremeValueMeasure_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hs ha.le)]
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure hs m ξ
  let _ := isProbabilityMeasure_generalizedExtremeValueMeasure (mul_pos hs ha)
    (m + s * ((Fintype.card ι : ℝ) ^ ξ - 1) / ξ) ξ
  have hindep : iIndepFun (fun i (x : ι → ℝ) => x i)
      (Measure.pi fun _ : ι => generalizedExtremeValueMeasure m s ξ) :=
    iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) fun _ => aemeasurable_id
  have hlaw (i : ι) : HasLaw (fun x : ι → ℝ => x i)
      (generalizedExtremeValueMeasure m s ξ)
      (Measure.pi fun _ : ι => generalizedExtremeValueMeasure m s ξ) :=
    (measurePreserving_eval (fun _ : ι => generalizedExtremeValueMeasure m s ξ) i).hasLaw
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_max_iid hindep hlaw x,
    cdf_generalizedExtremeValueMeasure_max Fintype.card_pos hs hξ]

/-- Independent generalized extreme-value variables with common parameters have a maximum
whose shape is unchanged and whose location and scale have the maximum-stability parameters. -/
theorem hasLaw_max_iid_generalizedExtremeValueMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (generalizedExtremeValueMeasure m s ξ) P) :
    HasLaw (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω)
      (generalizedExtremeValueMeasure
        (if ξ = 0 then m + s * Real.log (Fintype.card ι)
          else m + s * ((Fintype.card ι : ℝ) ^ ξ - 1) / ξ)
        (s * (Fintype.card ι : ℝ) ^ ξ) ξ) P := by
  rw [← map_max_pi_generalizedExtremeValueMeasure (ι := ι)]
  have hmax : Measurable (fun x : ι → ℝ => Finset.univ.sup' Finset.univ_nonempty x) := by
    simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup fun i => measurable_pi_apply i
  exact (hasLaw_map hmax.aemeasurable).comp (hindep.hasLaw_pi hlaw)

end TauCeti.Probability
