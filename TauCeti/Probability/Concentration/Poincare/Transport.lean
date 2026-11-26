/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev

/-!
# Transport of Poincaré and logarithmic Sobolev inequalities along isometries and translations

The Poincaré inequality `MeasureTheory.Measure.PoincareInequality μ C` and the logarithmic Sobolev
inequality `MeasureTheory.Measure.LogSobolevInequality μ C` are invariant, with the same constant
`C`, under pushing `μ` forward along a real linear isometry equivalence or along a translation.
Both maps are smooth measurable embeddings that preserve the operator norm of the derivative of
every test function, so variance, entropy, integrability and gradient energy are transported
unchanged.

No hypothesis on `μ` or `C` is needed: the canonical predicates do not contain probability or
nonnegativity of the constant. The zero-dimensional case needs no special treatment, since
precomposition with a linear isometry equivalence preserves operator norms in every dimension.

## Main results

* `MeasureTheory.Measure.poincareInequality_map_linearIsometryEquiv_iff` and
  `MeasureTheory.Measure.logSobolevInequality_map_linearIsometryEquiv_iff`: for `e : E ≃ₗᵢ[ℝ] F`,
  `μ.map e` satisfies the inequality with constant `C` iff `μ` does.
* `MeasureTheory.Measure.poincareInequality_map_add_right_iff` and
  `MeasureTheory.Measure.logSobolevInequality_map_add_right_iff`: for `a : E`, `μ.map (· + a)`
  satisfies the inequality with constant `C` iff `μ` does.

## References

* The Poincaré transport interface is adapted from the
  [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean).
* D. Bakry, I. Gentil and M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*,
  Springer (2014), §5.1.
-/

public section

open MeasureTheory ProbabilityTheory

open scoped ContDiff

namespace MeasureTheory.Measure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  {μ : Measure E} {C : ℝ}

/-- Push a Poincaré inequality forward along a smooth measurable embedding that preserves the
operator norm of the derivative of every test function. -/
private theorem PoincareInequality.map_of_norm_fderiv_comp (h : PoincareInequality μ C)
    {φ : E → F} (hφ : MeasurableEmbedding φ) (hφs : ContDiff ℝ ∞ φ)
    (hφd : ∀ (f : F → ℝ) (x : E), ‖fderiv ℝ (fun y ↦ f (φ y)) x‖ = ‖fderiv ℝ f (φ x)‖) :
    PoincareInequality (μ.map φ) C := by
  rw [PoincareInequality_def]
  intro f hf hfL hdf
  have hg : ContDiff ℝ ∞ (fun x ↦ f (φ x)) := hf.comp hφs
  have hgL : MemLp (fun x ↦ f (φ x)) 2 μ := hφ.memLp_map_measure_iff.1 hfL
  have hdg : MemLp (fun x ↦ ‖fderiv ℝ (fun y ↦ f (φ y)) x‖) 2 μ := by
    simp only [hφd]
    exact hφ.memLp_map_measure_iff.1 hdf
  rw [variance_map hfL.aemeasurable hφ.measurable.aemeasurable, hφ.integral_map]
  calc _ ≤ C * ∫ x, ‖fderiv ℝ (fun y ↦ f (φ y)) x‖ ^ 2 ∂μ := h.apply _ hg hgL hdg
    _ = C * ∫ x, ‖fderiv ℝ f (φ x)‖ ^ 2 ∂μ := by simp only [hφd]

/-- Push a logarithmic Sobolev inequality forward along a smooth measurable embedding that
preserves the operator norm of the derivative of every test function. -/
private theorem LogSobolevInequality.map_of_norm_fderiv_comp (h : LogSobolevInequality μ C)
    {φ : E → F} (hφ : MeasurableEmbedding φ) (hφs : ContDiff ℝ ∞ φ)
    (hφd : ∀ (f : F → ℝ) (x : E), ‖fderiv ℝ (fun y ↦ f (φ y)) x‖ = ‖fderiv ℝ f (φ x)‖) :
    LogSobolevInequality (μ.map φ) C :=
  (LogSobolevInequality_def _ _).2 fun f hf hdf hf2 hf2log ↦ by
  have hdg : MemLp (fun x ↦ ‖fderiv ℝ (fun y ↦ f (φ y)) x‖) 2 μ := by
    simpa only [hφd, Function.comp_def] using hφ.memLp_map_measure_iff.1 hdf
  rw [entropy_map hφ, hφ.integral_map]
  simpa only [hφd, Function.comp_def] using h.apply (fun y ↦ f (φ y)) (hf.comp hφs) hdg
    (hφ.integrable_map_iff.1 hf2) (hφ.integrable_map_iff.1 hf2log)

section LinearIsometryEquiv

variable [BorelSpace E] [BorelSpace F]

/-- Pushing a measure forward along a linear isometry equivalence preserves the Poincaré
inequality with the same constant. -/
theorem PoincareInequality.map_linearIsometryEquiv (h : PoincareInequality μ C)
    (e : E ≃ₗᵢ[ℝ] F) : PoincareInequality (μ.map e) C :=
  h.map_of_norm_fderiv_comp e.toHomeomorph.measurableEmbedding e.contDiff e.norm_fderiv_comp

/-- The Poincaré inequality with constant `C` is invariant under pushing the measure forward
along a linear isometry equivalence. -/
@[simp]
theorem poincareInequality_map_linearIsometryEquiv_iff (e : E ≃ₗᵢ[ℝ] F) :
    PoincareInequality (μ.map e) C ↔ PoincareInequality μ C :=
  ⟨fun h ↦ by
      convert h.map_linearIsometryEquiv e.symm
      simpa using (e.toHomeomorph.toMeasurableEquiv.map_symm_map (μ := μ)).symm,
    fun h ↦ h.map_linearIsometryEquiv e⟩

/-- Pushing a measure forward along a linear isometry equivalence preserves the logarithmic
Sobolev inequality with the same constant. -/
theorem LogSobolevInequality.map_linearIsometryEquiv (h : LogSobolevInequality μ C)
    (e : E ≃ₗᵢ[ℝ] F) : LogSobolevInequality (μ.map e) C :=
  h.map_of_norm_fderiv_comp e.toHomeomorph.measurableEmbedding e.contDiff e.norm_fderiv_comp

/-- The logarithmic Sobolev inequality with constant `C` is invariant under pushing the measure
forward along a linear isometry equivalence. -/
@[simp]
theorem logSobolevInequality_map_linearIsometryEquiv_iff (e : E ≃ₗᵢ[ℝ] F) :
    LogSobolevInequality (μ.map e) C ↔ LogSobolevInequality μ C :=
  ⟨fun h ↦ by
      convert h.map_linearIsometryEquiv e.symm
      simpa using (e.toHomeomorph.toMeasurableEquiv.map_symm_map (μ := μ)).symm,
    fun h ↦ h.map_linearIsometryEquiv e⟩

end LinearIsometryEquiv

section Translation

variable [BorelSpace E]

/-- Translating a measure preserves the Poincaré inequality with the same constant. -/
theorem PoincareInequality.map_add_right (h : PoincareInequality μ C) (a : E) :
    PoincareInequality (μ.map (· + a)) C :=
  h.map_of_norm_fderiv_comp (Homeomorph.addRight a).measurableEmbedding
    (contDiff_id.add contDiff_const) fun f x ↦ by rw [fderiv_comp_add_right]

/-- The Poincaré inequality with constant `C` is invariant under translating the measure. -/
@[simp]
theorem poincareInequality_map_add_right_iff (a : E) :
    PoincareInequality (μ.map (· + a)) C ↔ PoincareInequality μ C :=
  ⟨fun h ↦ by
      convert h.map_add_right (-a)
      simpa [Homeomorph.addRight_symm] using
        ((Homeomorph.addRight a).toMeasurableEquiv.map_symm_map (μ := μ)).symm,
    fun h ↦ h.map_add_right a⟩

/-- Translating a measure preserves the logarithmic Sobolev inequality with the same constant. -/
theorem LogSobolevInequality.map_add_right (h : LogSobolevInequality μ C) (a : E) :
    LogSobolevInequality (μ.map (· + a)) C :=
  h.map_of_norm_fderiv_comp (Homeomorph.addRight a).measurableEmbedding
    (contDiff_id.add contDiff_const) fun _ _ ↦ by rw [fderiv_comp_add_right]

/-- The logarithmic Sobolev inequality with constant `C` is invariant under translating the
measure. -/
@[simp]
theorem logSobolevInequality_map_add_right_iff (a : E) :
    LogSobolevInequality (μ.map (· + a)) C ↔ LogSobolevInequality μ C :=
  ⟨fun h ↦ by
      convert h.map_add_right (-a)
      simpa [Homeomorph.addRight_symm] using
        ((Homeomorph.addRight a).toMeasurableEquiv.map_symm_map (μ := μ)).symm,
    fun h ↦ h.map_add_right a⟩

end Translation

end MeasureTheory.Measure
