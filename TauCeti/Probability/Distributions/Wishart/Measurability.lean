/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Wishart.Basic

import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# Parameter measurability of the Gaussian-Gram Wishart distribution

The Gaussian-Gram Wishart law is measurable jointly in its natural degree and scale matrix. The
scale matrix is allowed to range over all matrices, in accordance with the totalized definition of
`multivariateGaussian`; in particular, no positive-semidefiniteness hypothesis is needed.

## Main results

* `TauCeti.measurable_wishartGramMeasure` — joint measurability in the natural degree and the
  entries of the scale matrix;
* `TauCeti.measurable_wishartGramMeasure_selfAdjoint` — the corresponding result when the scale
  ranges over the self-adjoint subspace.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace

namespace TauCeti

variable {p : ℕ}

private theorem measurable_wishartGramMeasure_fixedDegree (nu : ℕ) :
    Measurable fun S : Fin p → Fin p → ℝ =>
      wishartGramMeasure nu (Matrix.of S) := by
  have hGaussian : Measurable fun S : Fin p → Fin p → ℝ =>
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (Matrix.of S) :=
    measurable_multivariateGaussian.comp (measurable_const.prodMk measurable_id)
  have hpi : Measurable fun S : Fin p → Fin p → ℝ =>
      Measure.pi fun _ : Fin nu =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (Matrix.of S) := by
    simpa only [ProbabilityMeasure.toMeasure_pi, Measure.coe_toProbabilityMeasure] using
      TauCeti.MeasureTheory.measurable_probabilityMeasure_pi_const_toMeasure
        (fun S : Fin p → Fin p → ℝ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (Matrix.of S)).toProbabilityMeasure)
        hGaussian.subtype_mk
  rw [show (fun S : Fin p → Fin p → ℝ => wishartGramMeasure nu (Matrix.of S)) =
      fun S => (Measure.pi fun _ : Fin nu =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (Matrix.of S)).map wishartGram by
    funext S
    exact wishartGramMeasure_eq_map_pi nu (Matrix.of S)]
  exact (Measure.measurable_map (wishartGram (p := p) (ι := Fin nu))
    measurable_wishartGram).comp hpi

/-- The Gaussian-Gram Wishart law is jointly measurable in its natural degree and scale matrix.

The matrix is presented by its entries to make the coordinatewise product measurable structure
explicit. -/
@[fun_prop]
theorem measurable_wishartGramMeasure :
    Measurable fun q : ℕ × (Fin p → Fin p → ℝ) =>
      wishartGramMeasure q.1 (Matrix.of q.2) := by
  exact measurable_from_prod_countable_right fun nu =>
    measurable_wishartGramMeasure_fixedDegree nu

/-- The Gaussian-Gram Wishart law is jointly measurable when its scale ranges over the
self-adjoint subspace. -/
@[fun_prop]
theorem measurable_wishartGramMeasure_selfAdjoint :
    Measurable fun q : ℕ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      wishartGramMeasure q.1 (q.2 : Matrix (Fin p) (Fin p) ℝ) := by
  exact measurable_wishartGramMeasure.comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

end TauCeti
