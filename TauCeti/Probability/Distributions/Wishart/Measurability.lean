/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Basic

import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# Parameter measurability of the Gaussian-Gram Wishart family

This file proves that `TauCeti.wishartGramMeasure` is measurable jointly in its natural degree and
scale matrix.  The scale is first presented by all its coordinates, as required for a
matrix-parameterized probability kernel.  A second theorem restricts the scale to the symmetric
matrix carrier used by the Wishart law.

These results are what is needed to use the Gaussian-Gram Wishart law as a probability kernel
whose degree and scale are themselves random, for instance in hierarchical models or as a mixing
law.  No positive-semidefiniteness hypothesis on the scale is required, since the family is
defined for every real square matrix.

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
    exact measurable_multivariateGaussian.comp
      (measurable_const.prodMk (Matrix.measurable_of (Fin p) (Fin p) ℝ))
  -- `ProbabilityMeasure.toMeasure_pi` is a `rfl` lemma, so the product kernel can be stated
  -- directly as the `Measure.pi` appearing in `wishartGramMeasure_eq_map_pi`.
  have hpi : Measurable fun S : Fin p → Fin p → ℝ =>
      Measure.pi fun _ : Fin nu => multivariateGaussian 0 (Matrix.of S) :=
    MeasureTheory.measurable_probabilityMeasure_pi_const_toMeasure gaussian hgaussian
  have hmap : Measurable fun mu : Measure (Fin nu → EuclideanSpace ℝ (Fin p)) =>
      mu.map wishartGram := Measure.measurable_map wishartGram measurable_wishartGram
  simp only [wishartGramMeasure_eq_map_pi]
  exact hmap.comp hpi

/-- **Parameter measurability of the Gaussian-Gram Wishart law.** The law is measurable jointly
in its natural degree and every coordinate of its scale matrix.  No positivity hypothesis is
needed: outside the positive-semidefinite cone Mathlib's multivariate Gaussian, and hence this
family, is the appropriate Dirac law. -/
-- The statement follows `TauCetiRoadmap/StandardDistributions/Suggested.lean`, section
-- "Parameter measurability".
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
