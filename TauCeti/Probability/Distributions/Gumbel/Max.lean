/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gumbel.Basic
import TauCeti.Probability.Distributions.Relations

/-!
# Maxima of Gumbel variables

The maximum of `n > 0` independent Gumbel variables with location `m` and positive scale `s`
is Gumbel with location `m + s * log n` and the same scale. Thus subtracting `s * log n` from
the maximum recovers the original law exactly. This is the maximum-stability property of the
Gumbel family, in both product-measure and random-variable forms.

Maxima are taken over a nonempty finite type using `Finset.sup'`, so there is no arbitrary
empty-maximum convention. The proof specializes `cdf_max_iid` and identifies the resulting cdf
with the shifted Gumbel cdf.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), ch. 21.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι] {m s : ℝ}

/-- The maximum of a nonempty finite iid Gumbel sample has the same scale and location
increased by `s * log (Fintype.card ι)`. -/
theorem map_max_pi_gumbelMeasure (hs : 0 < s) (m : ℝ) :
    (Measure.pi fun _ : ι => gumbelMeasure m s).map
        (fun x => Finset.univ.sup' Finset.univ_nonempty x) =
      gumbelMeasure (m + s * Real.log (Fintype.card ι)) s := by
  let _ := isProbabilityMeasure_gumbelMeasure hs m
  let _ := isProbabilityMeasure_gumbelMeasure hs (m + s * Real.log (Fintype.card ι))
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hindep : iIndepFun (fun i (x : ι → ℝ) => x i)
      (Measure.pi fun _ : ι => gumbelMeasure m s) :=
    iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) fun _ => aemeasurable_id
  have hlaw (i : ι) : HasLaw (fun x : ι → ℝ => x i) (gumbelMeasure m s)
      (Measure.pi fun _ : ι => gumbelMeasure m s) :=
    (measurePreserving_eval (fun _ : ι => gumbelMeasure m s) i).hasLaw
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_max_iid hindep hlaw x, cdf_gumbelMeasure_eq hs, cdf_gumbelMeasure_eq hs,
    ← Real.exp_nat_mul]
  have hshift : -((x - (m + s * Real.log (Fintype.card ι))) / s) =
      Real.log (Fintype.card ι) + -((x - m) / s) := by
    field_simp
    ring
  rw [hshift, Real.exp_add, Real.exp_log hn]
  congr 1
  ring

/-- Independent Gumbel variables with a common positive scale and location have a Gumbel
maximum with location increased by the scale times the logarithm of the sample size. -/
theorem hasLaw_max_iid_gumbelMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → ℝ} (hs : 0 < s) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gumbelMeasure m s) P) :
    HasLaw (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω)
      (gumbelMeasure (m + s * Real.log (Fintype.card ι)) s) P := by
  rw [← map_max_pi_gumbelMeasure (ι := ι) hs]
  have hmax : Measurable (fun x : ι → ℝ => Finset.univ.sup' Finset.univ_nonempty x) := by
    simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup fun i => measurable_pi_apply i
  exact (hasLaw_map hmax.aemeasurable).comp (hindep.hasLaw_pi hlaw)

/-- Subtracting the logarithmic sample-size shift from the maximum of iid Gumbel variables
recovers their common law. -/
theorem hasLaw_max_sub_log_card_gumbelMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ι → Ω → ℝ} (hs : 0 < s) (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gumbelMeasure m s) P) :
    HasLaw (fun ω => (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) -
        s * Real.log (Fintype.card ι)) (gumbelMeasure m s) P := by
  have h := hasLaw_affine_gumbelMeasure one_pos (-s * Real.log (Fintype.card ι))
    (hasLaw_max_iid_gumbelMeasure hs hindep hlaw)
  simpa [sub_eq_add_neg, mul_assoc, add_comm, add_left_comm, add_assoc] using h

end TauCeti.Probability
