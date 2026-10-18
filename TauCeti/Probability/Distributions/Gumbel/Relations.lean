/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gumbel.Basic
public import TauCeti.Probability.Distributions.Relations

/-!
# Maximum stability of Gumbel laws

The maximum of a nonempty finite iid family is Gumbel: for `d` variables with location `m` and
scale `s`, its location is `m + s * log d` and its scale remains `s`.

The result is stated first as a measure identity and then as a random-variable law. It uses the
usual maximum convention for the Gumbel family.

## Main results

* `TauCeti.Probability.map_max_pi_gumbelMeasure` identifies the maximum under the product law;
* `ProbabilityTheory.iIndepFun.hasLaw_max_gumbelMeasure` gives the iid random-variable form.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 22.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {m s : ℝ}

/-- The maximum of a nonempty finite product of Gumbel laws has its location shifted by the
scale times the logarithm of the number of factors. -/
theorem map_max_pi_gumbelMeasure {ι : Type*} [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι => gumbelMeasure m s).map
        (fun x => Finset.univ.sup' Finset.univ_nonempty fun i => x i) =
      gumbelMeasure (m + s * Real.log (Fintype.card ι)) s := by
  rcases le_or_gt s 0 with hs | hs
  · have hpi : Measure.pi (fun _ : ι => gumbelMeasure m s) = 0 := by
      rw [show (fun _ : ι => gumbelMeasure m s) = fun _ => (0 : Measure ℝ) by
        funext i
        rw [gumbelMeasure_of_nonpos hs]]
      apply Measure.measure_univ_eq_zero.mp
      rw [Measure.pi_univ]
      apply Finset.prod_eq_zero (Finset.mem_univ (Classical.choice inferInstance))
      rfl
    rw [hpi, Measure.map_zero, gumbelMeasure_of_nonpos hs]
  let _ : IsProbabilityMeasure (gumbelMeasure m s) :=
    isProbabilityMeasure_gumbelMeasure hs m
  let _ : IsProbabilityMeasure (gumbelMeasure (m + s * Real.log (Fintype.card ι)) s) :=
    isProbabilityMeasure_gumbelMeasure hs _
  let X : ι → (ι → ℝ) → ℝ := fun i x => x i
  have hindep : iIndepFun X (Measure.pi fun _ : ι => gumbelMeasure m s) :=
    iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) fun _ => aemeasurable_id
  have hlaw : ∀ i, HasLaw (X i) (gumbelMeasure m s)
      (Measure.pi fun _ : ι => gumbelMeasure m s) := fun i =>
    (measurePreserving_eval (fun _ : ι => gumbelMeasure m s) i).hasLaw
  refine (Measure.cdf_eq_iff _ _).1 ?_
  ext x
  rw [cdf_max_iid hindep hlaw, cdf_gumbelMeasure_eq hs,
    cdf_gumbelMeasure_eq hs]
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [← Real.exp_nat_mul]
  congr 1
  have harg : -((x - (m + s * Real.log (Fintype.card ι))) / s) =
      Real.log (Fintype.card ι) + -((x - m) / s) := by
    field_simp [hs.ne']
    ring
  rw [harg, Real.exp_add, Real.exp_log hd]
  ring

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- The maximum of a nonempty finite iid family of Gumbel random variables is Gumbel, with its
location shifted by the scale times the logarithm of the family cardinality. -/
theorem iIndepFun.hasLaw_max_gumbelMeasure {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] {P : Measure Ω} {X : ι → Ω → ℝ}
    {m s : ℝ} (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) (gumbelMeasure m s) P) :
    HasLaw (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω)
      (gumbelMeasure (m + s * Real.log (Fintype.card ι)) s) P := by
  rw [← map_max_pi_gumbelMeasure (m := m)]
  have hmax : Measurable fun x : ι → ℝ =>
      Finset.univ.sup' Finset.univ_nonempty fun i => x i := by
    simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup fun i => measurable_pi_apply i
  exact (hasLaw_map hmax.aemeasurable).fun_comp (hindep.hasLaw_pi hlaw)

end ProbabilityTheory
