/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Wishart.Inverse.Basic

/-!
# Parameter measurability of the inverse-Wishart family

The inverse-Wishart law is measurable jointly in its real degree and scale matrix.
One result uses coordinates for matrix-parameterized kernels.
Another lets the scale range over symmetric matrices.
-/

public section

noncomputable section

open MeasureTheory

open scoped Matrix MatrixOrder

namespace TauCeti

variable {p : ℕ}

/-! ### Parameter measurability -/

/-- **Parameter measurability of the inverse-Wishart law.** The law is measurable jointly in its
real degree and every coordinate of its scale matrix, which is what an inverse-Wishart kernel with
a random degree and scale needs. -/
@[fun_prop]
theorem measurable_inverseWishartMeasure :
    Measurable fun q : ℝ × (Fin p → Fin p → ℝ) =>
      inverseWishartMeasure q.1 (Matrix.of q.2) := by
  have hcoords : Measurable fun q : ℝ × (Fin p → Fin p → ℝ) =>
      (q.1, (Matrix.ofMeasurableEquiv (Fin p) (Fin p) ℝ).symm ((Matrix.of q.2)⁻¹)) :=
    measurable_fst.prodMk
      ((Matrix.ofMeasurableEquiv (Fin p) (Fin p) ℝ).symm.measurable.comp
        (measurable_matrix_inv.comp ((Matrix.measurable_of (Fin p) (Fin p) ℝ).comp measurable_snd)))
  have hsource : Measurable fun q : ℝ × (Fin p → Fin p → ℝ) =>
      nonsingularWishartMeasure q.1 (Matrix.of q.2)⁻¹ := by
    simpa [Function.comp_def] using measurable_nonsingularWishartMeasure.comp hcoords
  simp only [inverseWishartMeasure_def]
  exact (Measure.measurable_map _ measurable_symmetricInv).comp hsource

/-- The inverse-Wishart law is measurable jointly in its real degree and a scale ranging over the
symmetric-matrix carrier. This is the form used to build a kernel with a random symmetric scale. -/
@[fun_prop]
theorem measurable_inverseWishartMeasure_selfAdjoint :
    Measurable fun q : ℝ × selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      inverseWishartMeasure q.1 (q.2 : Matrix (Fin p) (Fin p) ℝ) :=
  measurable_inverseWishartMeasure.comp
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))

end TauCeti
