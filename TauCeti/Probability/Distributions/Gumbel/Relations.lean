/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gumbel.Basic
public import TauCeti.Probability.Distributions.Relations

/-!
# Affine and maximum stability of Gumbel laws

Positive affine images of Gumbel laws remain Gumbel. The maximum of a nonempty finite iid
family is also Gumbel: for `d` variables with location `m` and scale `s`, its location is
`m + s * log d` and its scale remains `s`.

Both results are stated first as measure identities and then as random-variable laws. The maximum
identity uses the usual maximum convention for the Gumbel family.

## Main results

* `TauCeti.Probability.map_affine_gumbelMeasure` and
  `TauCeti.Probability.HasLaw.affine_gumbelMeasure` identify positive affine images;
* `TauCeti.Probability.map_max_pi_gumbelMeasure` identifies the maximum under the product law;
* `TauCeti.Probability.iIndepFun.hasLaw_max_gumbelMeasure` gives the iid random-variable form.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, 2nd ed.,
  Wiley (1994), ch. 21.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {m s a b : ℝ}

/-- A positive affine image of a Gumbel law is Gumbel, with the location and scale transformed
in the usual way. -/
theorem map_affine_gumbelMeasure (hs : 0 < s) (hb : 0 < b) :
    (gumbelMeasure m s).map (fun x => a + b * x) =
      gumbelMeasure (a + b * m) (b * s) := by
  rw [gumbelMeasure_of_pos hs, gumbelMeasure_of_pos (mul_pos hb hs),
    Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with x
  simp only [Function.comp_apply]
  ring

/-- A positive affine transform of a Gumbel random variable has the corresponding transformed
Gumbel law. -/
theorem HasLaw.affine_gumbelMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasLaw X (gumbelMeasure m s) P) (hs : 0 < s) (hb : 0 < b) :
    HasLaw (fun ω => a + b * X ω) (gumbelMeasure (a + b * m) (b * s)) P := by
  have hmap : HasLaw (fun x : ℝ => a + b * x) (gumbelMeasure (a + b * m) (b * s))
      (gumbelMeasure m s) :=
    ⟨by fun_prop, map_affine_gumbelMeasure (m := m) (s := s) (a := a) (b := b) hs hb⟩
  exact hmap.fun_comp hX

/-- The maximum of a nonempty finite product of Gumbel laws has its location shifted by the
scale times the logarithm of the number of factors. -/
theorem map_max_pi_gumbelMeasure {ι : Type*} [Fintype ι] [Nonempty ι] (hs : 0 < s) :
    (Measure.pi fun _ : ι => gumbelMeasure m s).map
        (fun x => Finset.univ.sup' Finset.univ_nonempty fun i => x i) =
      gumbelMeasure (m + s * Real.log (Fintype.card ι)) s := by
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

/-- The maximum of a nonempty finite iid family of Gumbel random variables is Gumbel, with its
location shifted by the scale times the logarithm of the family cardinality. -/
theorem iIndepFun.hasLaw_max_gumbelMeasure {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] {P : Measure Ω} {X : ι → Ω → ℝ}
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) (gumbelMeasure m s) P)
    (hs : 0 < s) :
    HasLaw (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => X i ω)
      (gumbelMeasure (m + s * Real.log (Fintype.card ι)) s) P := by
  rw [← map_max_pi_gumbelMeasure (m := m) hs]
  have hmax : Measurable fun x : ι → ℝ =>
      Finset.univ.sup' Finset.univ_nonempty fun i => x i := by
    simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup fun i => measurable_pi_apply i
  exact (hasLaw_map hmax.aemeasurable).fun_comp (hindep.hasLaw_pi hlaw)

end TauCeti.Probability
