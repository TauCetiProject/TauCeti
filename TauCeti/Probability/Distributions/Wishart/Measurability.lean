/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProductKernel
public import TauCeti.Probability.Distributions.Wishart.Basic

/-!
# Parameter measurability of the Gaussian-Gram Wishart family

This file proves that `TauCeti.wishartGramMeasure` is measurable jointly in its natural degree and
scale matrix.  The scale is first presented by all its coordinates, as required for a
matrix-parameterized probability kernel.  A second theorem restricts the scale to the symmetric
matrix carrier used by the Wishart law.

The proof writes the law as the image under `TauCeti.wishartGram` of a finite product of centered
multivariate Gaussian laws.  Mathlib supplies measurability of the multivariate Gaussian in its
mean and covariance, and `TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_const_toMeasure`
supplies measurability of the finite product.  Since the natural degree is countable, the
fixed-degree results assemble into a jointly measurable family.

## Main results

* `TauCeti.measurable_wishartGramMeasure` — joint measurability in the natural degree and all
  coordinates of the scale matrix;
* `TauCeti.measurable_wishartGramMeasure_selfAdjoint` — the corresponding result when the scale
  ranges over the symmetric-matrix carrier.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Matrix MatrixOrder

namespace TauCeti

variable {p : ℕ}

/-- At a fixed natural degree, the Gaussian-Gram Wishart law is measurable in all coordinates of
its scale matrix. -/
private theorem measurable_wishartGramMeasure_fixedDegree (nu : ℕ) :
    Measurable fun S : Fin p → Fin p → ℝ => wishartGramMeasure nu (Matrix.of S) := by
  let gaussian : (Fin p → Fin p → ℝ) → ProbabilityMeasure (EuclideanSpace ℝ (Fin p)) :=
    fun S => ⟨multivariateGaussian 0 (Matrix.of S), inferInstance⟩
  have hgaussian : Measurable gaussian := by
    apply Measurable.subtype_mk
    have hmatrix : Measurable fun S : Fin p → Fin p → ℝ => Matrix.of S :=
      Measurable.of_eval fun i => Measurable.of_eval fun j =>
        (measurable_pi_apply j).comp (measurable_pi_apply i)
    exact measurable_multivariateGaussian.comp (measurable_const.prodMk hmatrix)
  have hpi : Measurable fun S =>
      (ProbabilityMeasure.pi fun _ : Fin nu => gaussian S).toMeasure :=
    MeasureTheory.measurable_probabilityMeasure_pi_const_toMeasure gaussian hgaussian
  have hmap : Measurable fun mu : Measure (Fin nu → EuclideanSpace ℝ (Fin p)) =>
      mu.map wishartGram := Measure.measurable_map wishartGram measurable_wishartGram
  have hm := hmap.comp hpi
  have heq : (fun S =>
      (ProbabilityMeasure.pi fun _ : Fin nu => gaussian S).toMeasure.map wishartGram) =
      fun S => wishartGramMeasure nu (Matrix.of S) := by
    funext S
    exact (wishartGramMeasure_eq_map_pi nu (Matrix.of S)).symm
  change Measurable (fun S =>
    (ProbabilityMeasure.pi fun _ : Fin nu => gaussian S).toMeasure.map wishartGram) at hm
  rw [heq] at hm
  exact hm

/-- **Parameter measurability of the Gaussian-Gram Wishart law.** The law is measurable jointly
in its natural degree and every coordinate of its scale matrix.  No positivity hypothesis is
needed: outside the positive-semidefinite cone Mathlib's multivariate Gaussian, and hence this
family, is the appropriate Dirac law. -/
@[fun_prop]
theorem measurable_wishartGramMeasure :
    Measurable fun q : ℕ × (Fin p → Fin p → ℝ) =>
      wishartGramMeasure q.1 (Matrix.of q.2) :=
  measurable_from_prod_countable_right fun nu => measurable_wishartGramMeasure_fixedDegree nu

/-- The Gaussian-Gram Wishart law is measurable jointly in its natural degree and a scale ranging
over the symmetric-matrix carrier.  This is the form used to build a kernel with a random
symmetric scale. -/
@[fun_prop]
theorem measurable_wishartGramMeasure_selfAdjoint :
    Measurable fun q : ℕ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      wishartGramMeasure q.1 (q.2 : Matrix (Fin p) (Fin p) ℝ) := by
  exact measurable_wishartGramMeasure.comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

end TauCeti
