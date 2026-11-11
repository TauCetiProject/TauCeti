/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev

/-!
# Transport of the Poincaré inequality along isometries and translations

The Poincaré inequality `MeasureTheory.Measure.PoincareInequality μ C` is invariant, with the same
constant `C`, under pushing `μ` forward along a real linear isometry equivalence or along a
translation. Both maps are smooth measurable embeddings that preserve the operator norm of the
derivative of every test function, so variance, square-integrability and the gradient energy
are transported unchanged.

No hypothesis on `μ` or `C` is needed: the canonical predicate does not contain probability or
nonnegativity of the constant. The zero-dimensional case needs no special treatment, since
precomposition with a linear isometry equivalence preserves operator norms in every dimension.

## Main results

* `MeasureTheory.Measure.poincareInequality_map_linearIsometryEquiv_iff`: for `e : E ≃ₗᵢ[ℝ] F`,
  `μ.map e` satisfies the Poincaré inequality with constant `C` iff `μ` does.
* `MeasureTheory.Measure.poincareInequality_map_add_right_iff`: for `a : E`, `μ.map (· + a)`
  satisfies the Poincaré inequality with constant `C` iff `μ` does.

## References

* The transport interface is adapted from the
  [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean).
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

section LinearIsometryEquiv

variable [BorelSpace E] [BorelSpace F]

/-- Pushing a measure forward along a linear isometry equivalence preserves the Poincaré
inequality with the same constant. -/
theorem PoincareInequality.map_linearIsometryEquiv (h : PoincareInequality μ C)
    (e : E ≃ₗᵢ[ℝ] F) : PoincareInequality (μ.map e) C :=
  h.map_of_norm_fderiv_comp e.toHomeomorph.measurableEmbedding e.contDiff fun f x ↦ by
    have := e.toContinuousLinearEquiv.comp_right_fderiv (𝕜 := ℝ) (f := f) (x := x)
    simp only [Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv] at this
    rw [this]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e

/-- The Poincaré inequality with constant `C` is invariant under pushing the measure forward
along a linear isometry equivalence. -/
@[simp]
theorem poincareInequality_map_linearIsometryEquiv_iff (e : E ≃ₗᵢ[ℝ] F) :
    PoincareInequality (μ.map e) C ↔ PoincareInequality μ C := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map_linearIsometryEquiv e⟩
  have := h.map_linearIsometryEquiv e.symm
  rwa [Measure.map_map e.symm.continuous.measurable e.continuous.measurable,
    LinearIsometryEquiv.symm_comp_self, Measure.map_id] at this

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
    PoincareInequality (μ.map (· + a)) C ↔ PoincareInequality μ C := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map_add_right a⟩
  have h' := h.map_add_right (-a)
  have hcancel : ((· + -a) ∘ (· + a) : E → E) = id :=
    funext fun x ↦ add_neg_cancel_right x a
  rwa [Measure.map_map (measurable_add_const _) (measurable_add_const _),
    hcancel, Measure.map_id] at h'

end Translation

end MeasureTheory.Measure
