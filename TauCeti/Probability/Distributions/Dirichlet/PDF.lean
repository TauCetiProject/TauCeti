/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Density

/-!
# Density interfaces for Dirichlet coordinates

Dropping any one coordinate of a Dirichlet vector gives a law with density
`dirichletChartPDF` against product Lebesgue measure on the remaining coordinates.
This file identifies that coordinate law, its Radon–Nikodym derivative, and the canonical
pdf of the coordinates of a random vector with the Dirichlet law.

These are lower-dimensional density statements, not assertions of absolute continuity
against volume on the ambient Euclidean space. They include a single-category simplex:
the remaining coordinate space then has dimension zero. Positive shapes are required,
since the chart-density formula does not share the law's invalid-parameter totalization.

The construction is `dirichletMeasure_eq_map_withDensity_dirichletChartPDF`; the density
interfaces use the general `hasPDF_of_hasLaw_withDensity` and
`pdf_eq_of_hasLaw_withDensity` bridges.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ι → ℝ}

/-- Deleting one coordinate of a Dirichlet vector gives Lebesgue measure weighted by its
simplex-chart density. -/
theorem map_coords_dirichletMeasure_eq_withDensity (ha : ∀ i, 0 < a i) (i₀ : ι) :
    (dirichletMeasure a).map (fun x (j : {i // i ≠ i₀}) ↦ x j) =
      volume.withDensity (dirichletChartPDF a i₀) := by
  rw [dirichletMeasure_eq_map_withDensity_dirichletChartPDF ha i₀,
    Measure.map_map (by fun_prop) measurable_dirichletChart]
  have hcomp : (fun x (j : {i // i ≠ i₀}) ↦ x j) ∘ dirichletChart i₀ = id := by
    ext x j
    exact dirichletChart_apply_coe i₀ x j
  rw [hcomp, Measure.map_id]

/-- The Radon–Nikodym derivative of the deleted-coordinate law is the Dirichlet chart density. -/
theorem rnDeriv_map_coords_dirichletMeasure (ha : ∀ i, 0 < a i) (i₀ : ι) :
    ((dirichletMeasure a).map fun x (j : {i // i ≠ i₀}) ↦ x j).rnDeriv volume
      =ᵐ[volume] dirichletChartPDF a i₀ := by
  rw [map_coords_dirichletMeasure_eq_withDensity ha i₀]
  exact Measure.rnDeriv_withDensity _ (measurable_dirichletChartPDF a i₀)

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι} {a : ι → ℝ}

/-- The coordinates away from a chosen category of a Dirichlet random vector have the
chart-density law. -/
theorem dirichlet_coords (hX : HasLaw X (dirichletMeasure a) P)
    (ha : ∀ i, 0 < a i) (i₀ : ι) :
    HasLaw (fun ω (j : {i // i ≠ i₀}) ↦ X ω j)
      (volume.withDensity (dirichletChartPDF a i₀)) P := by
  rw [← map_coords_dirichletMeasure_eq_withDensity ha i₀]
  exact HasLaw.comp ⟨(by fun_prop : Measurable fun (x : EuclideanSpace ℝ ι)
    (j : {i // i ≠ i₀}) ↦ x j).aemeasurable, rfl⟩ hX

/-- The deleted coordinates of a Dirichlet random vector admit a density against product
Lebesgue measure. -/
theorem hasPDF_dirichlet_coords (hX : HasLaw X (dirichletMeasure a) P)
    (ha : ∀ i, 0 < a i) (i₀ : ι) :
    HasPDF (fun ω (j : {i // i ≠ i₀}) ↦ X ω j) P :=
  hasPDF_of_hasLaw_withDensity (measurable_dirichletChartPDF a i₀).aemeasurable
    (hX.dirichlet_coords ha i₀)

/-- The canonical pdf of the deleted coordinates of a Dirichlet random vector agrees almost
everywhere with the chart density. -/
theorem pdf_dirichlet_coords (hX : HasLaw X (dirichletMeasure a) P)
    (ha : ∀ i, 0 < a i) (i₀ : ι) :
    pdf (fun ω (j : {i // i ≠ i₀}) ↦ X ω j) P =ᵐ[volume] dirichletChartPDF a i₀ :=
  pdf_eq_of_hasLaw_withDensity (measurable_dirichletChartPDF a i₀).aemeasurable
    (hX.dirichlet_coords ha i₀)

end ProbabilityTheory.HasLaw
