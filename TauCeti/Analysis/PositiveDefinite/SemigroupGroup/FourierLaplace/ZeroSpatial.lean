/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Existence

/-!
# The zero-spatial Berg--Christensen--Ressel theorem

When the spatial inner-product space in the Berg--Christensen--Ressel representation is the
zero space `PUnit`, its Laplace--Fourier transform has no Fourier factor and is just a Laplace
transform.  This file makes that specialization precise at both the measure and theorem levels.

The measurable equivalence `ℝ≥0 × PUnit ≃ᵐ ℝ≥0` identifies finite representing measures.  Under
this equivalence, `TauCeti.RepresentsLaplaceFourier` for the function
`(t, _) ↦ f t` is exactly `TauCeti.RepresentsLaplace` for `f`.  Consequently the bounded,
continuous positive-definite condition in the BCR theorem is equivalent to complete monotonicity
on the closed half-line.  Thus the zero-spatial case of BCR is precisely the
Hausdorff--Bernstein--Widder theorem, including uniqueness of the representing measure.

## Main declarations

* `TauCeti.laplaceFourierTransform_map_prodPUnit_symm`: transporting a measure from `ℝ≥0` to
  `ℝ≥0 × PUnit` turns its Laplace--Fourier transform into its Laplace transform.
* `TauCeti.representsLaplaceFourier_map_prodPUnit_symm_iff`: the corresponding equivalence of
  representation predicates.
* `TauCeti.bcr_zero_spatial_iff_hausdorff_bernstein_widder`: the BCR hypotheses with zero spatial
  variable are equivalent to complete monotonicity.
* `TauCeti.eq_map_prodPUnit_symm_bernsteinMeasure`: the unique BCR representing measure in the
  zero-spatial case is the transported Bernstein measure.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.
* D. V. Widder, *The Laplace Transform*, Chapter IV.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti

/-- The Laplace--Fourier transform of a measure transported to `ℝ≥0 × PUnit` is its ordinary
Laplace transform, viewed in `ℂ`. -/
@[simp]
theorem laplaceFourierTransform_map_prodPUnit_symm (μ : Measure ℝ≥0) (t : ℝ≥0)
    (u : PUnit.{1}) :
    laplaceFourierTransform
        (μ.map (MeasurableEquiv.prodPUnit : ℝ≥0 × PUnit.{1} ≃ᵐ ℝ≥0).symm) (t, u) =
      (laplaceTransform μ t : ℂ) := by
  rw [laplaceFourierTransform_apply, integral_map_equiv, laplaceTransform_apply]
  rw [Subsingleton.elim u 0]
  -- `integral_map_equiv` retains the opaque projections of `prodPUnit.symm`; expose their
  -- pointwise values so the two transform kernels can be compared.
  change (∫ p : ℝ≥0, laplaceAtom t p * fourierAtom (0 : PUnit.{1}) 0 ∂μ) =
    (↑(∫ p : ℝ≥0, Real.exp (-(t * p : ℝ)) ∂μ) : ℂ)
  simp only [fourierAtom_zero_left, mul_one, laplaceAtom_def]
  calc
    (∫ p : ℝ≥0, (Real.exp (-p * t : ℝ) : ℂ) ∂μ) =
        (↑(∫ p : ℝ≥0, Real.exp (-p * t : ℝ) ∂μ) : ℂ) := integral_ofReal
    _ = (↑(∫ p : ℝ≥0, Real.exp (-(t * p : ℝ)) ∂μ) : ℂ) := by
      apply congrArg Complex.ofReal
      apply integral_congr_ae
      filter_upwards with p
      congr 1
      ring

/-- In zero spatial dimension, Laplace--Fourier representation of `(t, _) ↦ f t` by the
transported measure is exactly ordinary Laplace representation of `f`. -/
theorem representsLaplaceFourier_map_prodPUnit_symm_iff (μ : Measure ℝ≥0) (f : ℝ → ℝ) :
    RepresentsLaplaceFourier
        (μ.map (MeasurableEquiv.prodPUnit : ℝ≥0 × PUnit.{1} ≃ᵐ ℝ≥0).symm)
        (fun x : ℝ≥0 × PUnit.{1} => (f x.1 : ℂ)) ↔
      RepresentsLaplace μ f := by
  constructor
  · intro h
    let _ : IsFiniteMeasure
        (μ.map (MeasurableEquiv.prodPUnit : ℝ≥0 × PUnit.{1} ≃ᵐ ℝ≥0).symm) := by
      exact h.isFiniteMeasure
    have hμfin : IsFiniteMeasure μ := Measure.isFiniteMeasure_of_map
      (MeasurableEquiv.prodPUnit : ℝ≥0 × PUnit.{1} ≃ᵐ ℝ≥0).symm.measurable.aemeasurable
    refine representsLaplace_iff.mpr ⟨hμfin, fun t ht => ?_⟩
    have hrep := h.eq_laplaceFourierTransform ((⟨t, ht⟩ : ℝ≥0), PUnit.unit)
    rw [laplaceFourierTransform_map_prodPUnit_symm μ (⟨t, ht⟩ : ℝ≥0) PUnit.unit] at hrep
    exact_mod_cast hrep
  · intro h
    let _ : IsFiniteMeasure μ := h.isFiniteMeasure
    have hmap : IsFiniteMeasure
        (μ.map (MeasurableEquiv.prodPUnit : ℝ≥0 × PUnit.{1} ≃ᵐ ℝ≥0).symm) := inferInstance
    refine representsLaplaceFourier_iff.mpr ⟨hmap, ?_⟩
    rintro ⟨t, u⟩
    rw [laplaceFourierTransform_map_prodPUnit_symm]
    exact_mod_cast h.eq_laplaceTransform t.coe_nonneg

/-- A measure on `ℝ≥0 × PUnit` represents a zero-spatial function if and only if its time
marginal gives the corresponding Laplace representation. -/
@[simp]
theorem representsLaplaceFourier_zero_spatial_iff
    (μ : Measure (ℝ≥0 × PUnit.{1})) (f : ℝ → ℝ) :
    RepresentsLaplaceFourier μ (fun x : ℝ≥0 × PUnit.{1} => (f x.1 : ℂ)) ↔
      RepresentsLaplace
        (μ.map (MeasurableEquiv.prodPUnit : ℝ≥0 × PUnit.{1} ≃ᵐ ℝ≥0)) f := by
  rw [← representsLaplaceFourier_map_prodPUnit_symm_iff]
  simp only [MeasurableEquiv.map_symm_map]

/-- **The zero-spatial BCR theorem is the Hausdorff--Bernstein--Widder theorem.**

For a real function `f`, the bounded, continuous positive-definite condition on
`(t, _) ↦ f t : ℝ≥0 × PUnit → ℂ` holds exactly when `f` is continuous on `[0, ∞)` and completely
monotone on `(0, ∞)`. -/
theorem bcr_zero_spatial_iff_hausdorff_bernstein_widder (f : ℝ → ℝ) :
    (IsSemigroupGroupPD (fun x : ℝ≥0 × PUnit.{1} => (f x.1 : ℂ)) ∧
        Continuous (fun x : ℝ≥0 × PUnit.{1} => (f x.1 : ℂ)) ∧
        Bornology.IsBounded (range fun x : ℝ≥0 × PUnit.{1} => (f x.1 : ℂ))) ↔
      IsContinuousCompletelyMonotoneOnIoi f := by
  constructor
  · intro h
    obtain ⟨μ, hμ, -⟩ := (bcr_semigroup_bochner
      (fun x : ℝ≥0 × PUnit.{1} => (f x.1 : ℂ))).mp h
    exact RepresentsLaplace.isContinuousCompletelyMonotoneOnIoi
      ((representsLaplaceFourier_zero_spatial_iff μ f).mp hμ)
  · intro hf
    have hμ := representsLaplace_bernsteinMeasure hf
    apply (bcr_semigroup_bochner (fun x : ℝ≥0 × PUnit.{1} => (f x.1 : ℂ))).mpr
    refine ⟨(bernsteinMeasure f).map
        (MeasurableEquiv.prodPUnit : ℝ≥0 × PUnit.{1} ≃ᵐ ℝ≥0).symm,
      (representsLaplaceFourier_map_prodPUnit_symm_iff _ _).mpr hμ, ?_⟩
    intro ν hν
    exact hν.unique ((representsLaplaceFourier_map_prodPUnit_symm_iff _ _).mpr hμ)

/-- In zero spatial dimension, the transported Bernstein measure represents a function that is
continuous on `[0, ∞)` and completely monotone on `(0, ∞)`. -/
theorem representsLaplaceFourier_map_prodPUnit_symm_bernsteinMeasure {f : ℝ → ℝ}
    (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    RepresentsLaplaceFourier
      ((bernsteinMeasure f).map
        (MeasurableEquiv.prodPUnit : ℝ≥0 × PUnit.{1} ≃ᵐ ℝ≥0).symm)
      (fun x : ℝ≥0 × PUnit.{1} => (f x.1 : ℂ)) :=
  (representsLaplaceFourier_map_prodPUnit_symm_iff _ _).mpr
    (representsLaplace_bernsteinMeasure hf)

/-- Any zero-spatial BCR representing measure is the transported Bernstein measure. -/
theorem eq_map_prodPUnit_symm_bernsteinMeasure {f : ℝ → ℝ}
    (μ : Measure (ℝ≥0 × PUnit.{1}))
    (hμ : RepresentsLaplaceFourier μ (fun x : ℝ≥0 × PUnit.{1} => (f x.1 : ℂ))) :
    μ = (bernsteinMeasure f).map
      (MeasurableEquiv.prodPUnit : ℝ≥0 × PUnit.{1} ≃ᵐ ℝ≥0).symm := by
  have hf := RepresentsLaplace.isContinuousCompletelyMonotoneOnIoi
    ((representsLaplaceFourier_zero_spatial_iff μ f).mp hμ)
  exact hμ.unique (representsLaplaceFourier_map_prodPUnit_symm_bernsteinMeasure hf)

end TauCeti

end

end
