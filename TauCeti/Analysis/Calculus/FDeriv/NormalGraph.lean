/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.WithLp
public import TauCeti.Analysis.Calculus.FDeriv.Parametrization
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Differentiation of functions on normal graphs

A derivative of the pullback of a function by `TauCeti.normalGraphEmbedding φ` gives a
within-derivative on the graph: compose the pullback derivative with the second projection.
The graphing function need not be differentiable for this construction.

At a differentiability point of `φ`, all within-derivatives on the graph have the same
restriction to its tangent plane, the range of the linear graph of `Dφ`. Thus the tangential
derivative is intrinsic even though its extension to the ambient space is not unique.
The pullback construction and differentiability equivalence also hold for graphs restricted
to an arbitrary parameter set.
-/

public section

open Set

namespace HasFDerivWithinAt

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {A : E →L[ℝ] ℝ} {B : E →L[ℝ] F}
  {M M₁ M₂ : WithLp 2 (ℝ × E) →L[ℝ] F} {s : Set E} {x : E}

/-- A within-derivative of the pullback gives a within-derivative on the graph by composing
with the second projection. No regularity of the graphing function is required. -/
theorem of_comp_normalGraphEmbedding
    (h : HasFDerivWithinAt (f ∘ TauCeti.normalGraphEmbedding φ) B s x) :
    HasFDerivWithinAt f (B.comp (WithLp.sndL 2 ℝ ℝ E))
      (TauCeti.normalGraphEmbedding φ '' s) (TauCeti.normalGraphEmbedding φ x) := by
  exact h.of_comp_of_leftInvOn (WithLp.sndL 2 ℝ ℝ E).hasFDerivAt.hasFDerivWithinAt
    (fun y _ => TauCeti.normalGraphEmbedding_snd φ y)

/-- Pulling a graph within-derivative back along the linear graph of `A` recovers the
parameter derivative, provided derivatives on the parameter set are unique. -/
theorem comp_normalGraphL_eq
    (hM : HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (hφ : HasFDerivWithinAt φ A s x)
    (hB : HasFDerivWithinAt (f ∘ TauCeti.normalGraphEmbedding φ) B s x)
    (hs : UniqueDiffWithinAt ℝ s x) : M.comp A.normalGraphL = B :=
  hs.eq (hM.comp x hφ.normalGraphEmbedding (mapsTo_image _ _)) hB

/-- Two within-derivatives on a differentiable graph agree on its tangent plane when the
parameter set has unique derivatives at the parameter point. -/
theorem comp_subtypeL_range_normalGraphL_eq
    (h₁ : HasFDerivWithinAt f M₁ (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (h₂ : HasFDerivWithinAt f M₂ (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (hφ : HasFDerivWithinAt φ A s x) (hs : UniqueDiffWithinAt ℝ s x) :
    M₁.comp A.normalGraphL.range.subtypeL = M₂.comp A.normalGraphL.range.subtypeL := by
  exact h₁.comp_subtypeL_range_eq h₂ hφ.normalGraphEmbedding hs

/-- When `φ` is differentiable within `s` and `s` has unique derivatives at the parameter
point, the tangential derivative is the pullback derivative composed with the second projection
and restricted to the tangent plane. -/
theorem comp_subtypeL_range_normalGraphL_eq_of_comp_normalGraphEmbedding
    (hM : HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (hφ : HasFDerivWithinAt φ A s x)
    (hB : HasFDerivWithinAt (f ∘ TauCeti.normalGraphEmbedding φ) B s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    M.comp A.normalGraphL.range.subtypeL =
      (B.comp (WithLp.sndL 2 ℝ ℝ E)).comp A.normalGraphL.range.subtypeL :=
  (M.comp_subtypeL_range_normalGraphL_eq_iff A B).mpr (hM.comp_normalGraphL_eq hφ hB hs)

end HasFDerivWithinAt

namespace DifferentiableWithinAt

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {A : E →L[ℝ] ℝ} {s : Set E} {x : E}

/-- On a differentiable graph, differentiability within the graph is equivalent to
within-differentiability of the pullback on the parameter set. -/
theorem normalGraphEmbedding_image_iff
    (hφ : DifferentiableWithinAt ℝ φ s x) :
    DifferentiableWithinAt ℝ f (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x) ↔
      DifferentiableWithinAt ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s x := by
  exact hφ.hasFDerivWithinAt.normalGraphEmbedding.differentiableWithinAt.image_iff_of_leftInvOn
    (WithLp.sndL 2 ℝ ℝ E).differentiableAt.differentiableWithinAt
    (fun y _ => TauCeti.normalGraphEmbedding_snd φ y)

/-- A function differentiable within a differentiable graph has a unique derivative
restricted to the tangent plane when the parameter set has unique derivatives. -/
theorem existsUnique_hasFDerivWithinAt_normalGraphEmbedding_image_comp_subtypeL
    (hf : DifferentiableWithinAt ℝ f (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (hφ : HasFDerivWithinAt φ A s x) (hs : UniqueDiffWithinAt ℝ s x) :
    ∃! D : A.normalGraphL.range →L[ℝ] F,
      ∃ M : WithLp 2 (ℝ × E) →L[ℝ] F,
        HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s)
          (TauCeti.normalGraphEmbedding φ x) ∧
        M.comp A.normalGraphL.range.subtypeL = D := by
  exact hf.existsUnique_hasFDerivWithinAt_image_comp_subtypeL hφ.normalGraphEmbedding hs

/-- On a graph with `φ` differentiable within `s` and unique parameter derivatives at `x`,
the chosen graph within-derivative pulls back to the chosen parameter derivative.
This also holds when the function is not differentiable, as both sides then vanish. -/
theorem fderivWithin_normalGraphEmbedding_image_comp_normalGraphL
    (hφ : DifferentiableWithinAt ℝ φ s x) (hs : UniqueDiffWithinAt ℝ s x) :
    (fderivWithin ℝ f (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x)).comp (fderivWithin ℝ φ s x).normalGraphL =
      fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s x := by
  simpa only [hφ.hasFDerivWithinAt.normalGraphEmbedding.fderivWithin hs] using
    DifferentiableWithinAt.fderivWithin_image_comp_of_leftInvOn (f := f)
      hφ.hasFDerivWithinAt.normalGraphEmbedding.differentiableWithinAt
      (WithLp.sndL 2 ℝ ℝ E).differentiableAt.differentiableWithinAt
      (fun y _ => TauCeti.normalGraphEmbedding_snd φ y) hs

/-- When `φ` is differentiable within `s` and `s` has unique derivatives at the parameter
point, restricting the chosen graph derivative to the tangent plane gives the pullback
parameter derivative composed with the second projection on that plane. -/
theorem fderivWithin_normalGraphEmbedding_image_comp_subtypeL
    (hφ : DifferentiableWithinAt ℝ φ s x) (hs : UniqueDiffWithinAt ℝ s x) :
    (fderivWithin ℝ f (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x)).comp
        (fderivWithin ℝ φ s x).normalGraphL.range.subtypeL =
      ((fderivWithin ℝ (f ∘ TauCeti.normalGraphEmbedding φ) s x).comp
        (WithLp.sndL 2 ℝ ℝ E)).comp (fderivWithin ℝ φ s x).normalGraphL.range.subtypeL := by
  exact (ContinuousLinearMap.comp_subtypeL_range_normalGraphL_eq_iff _ _ _).mpr
    (hφ.fderivWithin_normalGraphEmbedding_image_comp_normalGraphL hs)

end DifferentiableWithinAt

namespace HasFDerivAt

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {B : E →L[ℝ] F} {x : E}

/-- A derivative of the pullback gives a within-derivative on the full graph.
No differentiability of the graphing function is required. -/
theorem hasFDerivWithinAt_range_of_comp_normalGraphEmbedding
    (h : HasFDerivAt (f ∘ TauCeti.normalGraphEmbedding φ) B x) :
    HasFDerivWithinAt f (B.comp (WithLp.sndL 2 ℝ ℝ E))
      (range (TauCeti.normalGraphEmbedding φ)) (TauCeti.normalGraphEmbedding φ x) := by
  simpa only [image_univ] using
    h.hasFDerivWithinAt.of_comp_normalGraphEmbedding (s := univ)

end HasFDerivAt

namespace HasFDerivWithinAt

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {A : E →L[ℝ] ℝ} {B : E →L[ℝ] F}
  {M M₁ M₂ : WithLp 2 (ℝ × E) →L[ℝ] F} {x : E}

/-- A within-derivative on the full graph pulls back to the parameter derivative. -/
theorem comp_normalGraphL_eq_of_range
    (hM : HasFDerivWithinAt f M (range (TauCeti.normalGraphEmbedding φ))
      (TauCeti.normalGraphEmbedding φ x))
    (hφ : HasFDerivAt φ A x) (hB : HasFDerivAt (f ∘ TauCeti.normalGraphEmbedding φ) B x) :
    M.comp A.normalGraphL = B := by
  rw [← image_univ] at hM
  exact hM.comp_normalGraphL_eq hφ.hasFDerivWithinAt hB.hasFDerivWithinAt
    uniqueDiffWithinAt_univ

/-- Two within-derivatives on the full graph agree on its tangent plane. -/
theorem comp_subtypeL_range_normalGraphL_eq_of_range
    (h₁ : HasFDerivWithinAt f M₁ (range (TauCeti.normalGraphEmbedding φ))
      (TauCeti.normalGraphEmbedding φ x))
    (h₂ : HasFDerivWithinAt f M₂ (range (TauCeti.normalGraphEmbedding φ))
      (TauCeti.normalGraphEmbedding φ x)) (hφ : HasFDerivAt φ A x) :
    M₁.comp A.normalGraphL.range.subtypeL = M₂.comp A.normalGraphL.range.subtypeL := by
  rw [← image_univ] at h₁ h₂
  exact h₁.comp_subtypeL_range_normalGraphL_eq h₂ hφ.hasFDerivWithinAt
    uniqueDiffWithinAt_univ

/-- On the full graph, the tangential derivative is the pullback derivative composed
with the second projection and restricted to the tangent plane. -/
theorem comp_subtypeL_range_normalGraphL_eq_of_comp_normalGraphEmbedding_of_range
    (hM : HasFDerivWithinAt f M (range (TauCeti.normalGraphEmbedding φ))
      (TauCeti.normalGraphEmbedding φ x))
    (hφ : HasFDerivAt φ A x) (hB : HasFDerivAt (f ∘ TauCeti.normalGraphEmbedding φ) B x) :
    M.comp A.normalGraphL.range.subtypeL =
      (B.comp (WithLp.sndL 2 ℝ ℝ E)).comp A.normalGraphL.range.subtypeL :=
  (M.comp_subtypeL_range_normalGraphL_eq_iff A B).mpr
    (hM.comp_normalGraphL_eq_of_range hφ hB)

end HasFDerivWithinAt

namespace DifferentiableAt

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {x : E}

/-- On the full differentiable graph, within-differentiability is equivalent to
differentiability of the pullback on the parameter space. -/
theorem differentiableWithinAt_range_normalGraphEmbedding_iff (hφ : DifferentiableAt ℝ φ x) :
    DifferentiableWithinAt ℝ f (range (TauCeti.normalGraphEmbedding φ))
      (TauCeti.normalGraphEmbedding φ x) ↔
      DifferentiableAt ℝ (f ∘ TauCeti.normalGraphEmbedding φ) x := by
  simpa only [image_univ, differentiableWithinAt_univ] using
    hφ.differentiableWithinAt.normalGraphEmbedding_image_iff (f := f) (s := univ)

/-- The chosen within-derivative on the full graph pulls back to the parameter derivative. -/
theorem fderivWithin_range_normalGraphEmbedding_comp_normalGraphL
    (hφ : DifferentiableAt ℝ φ x) :
    (fderivWithin ℝ f (range (TauCeti.normalGraphEmbedding φ))
      (TauCeti.normalGraphEmbedding φ x)).comp (fderiv ℝ φ x).normalGraphL =
      fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) x := by
  simpa only [image_univ, fderivWithin_univ] using
    hφ.differentiableWithinAt.fderivWithin_normalGraphEmbedding_image_comp_normalGraphL
      (f := f) uniqueDiffWithinAt_univ

/-- The chosen derivative on the full graph has the canonical restriction to its tangent plane. -/
theorem fderivWithin_range_normalGraphEmbedding_comp_subtypeL
    (hφ : DifferentiableAt ℝ φ x) :
    (fderivWithin ℝ f (range (TauCeti.normalGraphEmbedding φ))
      (TauCeti.normalGraphEmbedding φ x)).comp (fderiv ℝ φ x).normalGraphL.range.subtypeL =
      ((fderiv ℝ (f ∘ TauCeti.normalGraphEmbedding φ) x).comp
        (WithLp.sndL 2 ℝ ℝ E)).comp (fderiv ℝ φ x).normalGraphL.range.subtypeL := by
  exact (ContinuousLinearMap.comp_subtypeL_range_normalGraphL_eq_iff _ _ _).mpr
    hφ.fderivWithin_range_normalGraphEmbedding_comp_normalGraphL

end DifferentiableAt

namespace DifferentiableWithinAt

/-- A function differentiable within the full differentiable graph has a unique derivative
restricted to its tangent plane. -/
theorem existsUnique_hasFDerivWithinAt_range_normalGraphEmbedding_comp_subtypeL
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {A : E →L[ℝ] ℝ} {x : E}
    (hf : DifferentiableWithinAt ℝ f (range (TauCeti.normalGraphEmbedding φ))
      (TauCeti.normalGraphEmbedding φ x)) (hφ : HasFDerivAt φ A x) :
    ∃! D : A.normalGraphL.range →L[ℝ] F,
      ∃ M : WithLp 2 (ℝ × E) →L[ℝ] F,
        HasFDerivWithinAt f M (range (TauCeti.normalGraphEmbedding φ))
          (TauCeti.normalGraphEmbedding φ x) ∧
        M.comp A.normalGraphL.range.subtypeL = D := by
  rw [← image_univ] at hf ⊢
  exact hf.existsUnique_hasFDerivWithinAt_normalGraphEmbedding_image_comp_subtypeL
    hφ.hasFDerivWithinAt uniqueDiffWithinAt_univ

end DifferentiableWithinAt
