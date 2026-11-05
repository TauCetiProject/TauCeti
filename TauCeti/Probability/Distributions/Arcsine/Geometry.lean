/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Arcsine.Basic
public import TauCeti.Probability.Distributions.Uniform.Sphere.Coordinate
public import TauCeti.Probability.Distributions.Uniform.Sphere.Circle

/-!
# The arcsine law from uniform circle coordinates

A coordinate of a uniform planar unit vector, shifted and divided by two, has the
unit-interval arcsine law. The cosine and sine of a Haar-uniform angle give the same
construction. These measure identities connect the Beta realization of the arcsine
law to uniform directions, and allow its density, cdf and quantiles to be used for
circular observables.

The circle-coordinate law is the two-dimensional case of
`map_add_one_div_two_eval_uniformSphereMeasure`. The homeomorphism
`circleSphereHomeomorph` identifies angles with planar unit vectors.

## References

* K.-T. Fang, S. Kotz, K. W. Ng, *Symmetric Multivariate and Related Distributions*,
  Chapman and Hall, 1990, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real AddCircle

namespace TauCeti.Probability

/-- A rescaled coordinate of a uniform unit vector in two dimensions is arcsine. -/
@[simp] theorem map_add_one_div_two_eval_uniformSphereMeasure_eq_arcsineMeasure
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 2) (i : ι) :
    (uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun x ↦ (x.val i + 1) / 2) =
      arcsineMeasure := by
  let _ : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rw [map_add_one_div_two_eval_uniformSphereMeasure, arcsineMeasure_eq_betaMeasure]
  norm_num [hι]

/-- A Haar-uniform angle gives an arcsine variable by rescaling its cosine to `[0, 1]`. -/
@[simp] theorem map_add_one_div_two_cos_haarAddCircle :
    (@haarAddCircle (2 * π) ⟨two_pi_pos⟩).map
      (fun θ ↦ (cos_periodic.lift θ + 1) / 2) = arcsineMeasure := by
  have h := map_add_one_div_two_eval_uniformSphereMeasure_eq_arcsineMeasure
    (by decide : Fintype.card (Fin 2) = 2) (0 : Fin 2)
  rw [← map_circleSphereHomeomorph_haarAddCircle,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  convert h using 1
  congr 1
  funext θ
  induction θ using QuotientAddGroup.induction_on with | H t =>
  simp

/-- A Haar-uniform angle gives an arcsine variable by rescaling its sine to `[0, 1]`. -/
@[simp] theorem map_add_one_div_two_sin_haarAddCircle :
    (@haarAddCircle (2 * π) ⟨two_pi_pos⟩).map
      (fun θ ↦ (sin_periodic.lift θ + 1) / 2) = arcsineMeasure := by
  have h := map_add_one_div_two_eval_uniformSphereMeasure_eq_arcsineMeasure
    (by decide : Fintype.card (Fin 2) = 2) (1 : Fin 2)
  rw [← map_circleSphereHomeomorph_haarAddCircle,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  convert h using 1
  congr 1
  funext θ
  induction θ using QuotientAddGroup.induction_on with | H t =>
  simp

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Rescaling a coordinate of a uniform planar direction gives an arcsine random variable. -/
theorem HasLaw.add_one_div_two_eval_uniformSphereMeasure_arcsine
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 2) (i : ι)
    {X : Ω → Metric.sphere (0 : EuclideanSpace ℝ ι) 1}
    (hX : HasLaw X (uniformSphereMeasure (EuclideanSpace ℝ ι)) P) :
    HasLaw (fun ω ↦ ((X ω).val i + 1) / 2) arcsineMeasure P :=
  (HasLaw.mk (by fun_prop)
    (map_add_one_div_two_eval_uniformSphereMeasure_eq_arcsineMeasure hι i)).fun_comp hX

/-- The rescaled cosine of a Haar-uniform angle has the arcsine law. -/
theorem HasLaw.add_one_div_two_cos_haarAddCircle
    {X : Ω → AddCircle (2 * π)}
    (hX : HasLaw X (@haarAddCircle (2 * π) ⟨two_pi_pos⟩) P) :
    HasLaw (fun ω ↦ (cos_periodic.lift (X ω) + 1) / 2) arcsineMeasure P := by
  have hc : Continuous (fun θ : AddCircle (2 * π) ↦ (cos_periodic.lift θ + 1) / 2) :=
    (Real.Angle.continuous_cos.add continuous_const).div_const 2
  exact (HasLaw.mk hc.measurable.aemeasurable map_add_one_div_two_cos_haarAddCircle).fun_comp hX

/-- The rescaled sine of a Haar-uniform angle has the arcsine law. -/
theorem HasLaw.add_one_div_two_sin_haarAddCircle
    {X : Ω → AddCircle (2 * π)}
    (hX : HasLaw X (@haarAddCircle (2 * π) ⟨two_pi_pos⟩) P) :
    HasLaw (fun ω ↦ (sin_periodic.lift (X ω) + 1) / 2) arcsineMeasure P := by
  have hc : Continuous (fun θ : AddCircle (2 * π) ↦ (sin_periodic.lift θ + 1) / 2) :=
    (Real.Angle.continuous_sin.add continuous_const).div_const 2
  exact (HasLaw.mk hc.measurable.aemeasurable map_add_one_div_two_sin_haarAddCircle).fun_comp hX

end ProbabilityTheory
