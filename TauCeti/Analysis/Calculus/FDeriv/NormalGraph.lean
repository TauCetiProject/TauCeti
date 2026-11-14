/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Comp
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
  have hπ := (WithLp.sndL 2 ℝ ℝ E).hasFDerivAt.hasFDerivWithinAt
    (s := TauCeti.normalGraphEmbedding φ '' s) (x := TauCeti.normalGraphEmbedding φ x)
  have hm : MapsTo (WithLp.sndL 2 ℝ ℝ E) (TauCeti.normalGraphEmbedding φ '' s) s := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  have h' : HasFDerivWithinAt (f ∘ TauCeti.normalGraphEmbedding φ) B s
      ((WithLp.sndL 2 ℝ ℝ E) (TauCeti.normalGraphEmbedding φ x)) := by
    simpa only [WithLp.sndL_apply, TauCeti.normalGraphEmbedding_snd] using h
  have hc := h'.comp (TauCeti.normalGraphEmbedding φ x) hπ hm
  apply hc.congr
  · rintro _ ⟨y, _, rfl⟩
    simp
  · simp

/-- Pulling a within-derivative back to a differentiable graph recovers the parameter
derivative, provided derivatives on the parameter set are unique. -/
theorem comp_normalGraphL_eq
    (hM : HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (hφ : HasFDerivWithinAt φ A s x)
    (hB : HasFDerivWithinAt (f ∘ TauCeti.normalGraphEmbedding φ) B s x)
    (hs : UniqueDiffWithinAt ℝ s x) : M.comp A.normalGraphL = B :=
  hs.eq (hM.comp x hφ.normalGraphEmbedding (mapsTo_image _ _)) hB

/-- Two within-derivatives on a differentiable graph agree on its tangent plane. -/
theorem comp_subtypeL_normalGraphL_range_eq
    (h₁ : HasFDerivWithinAt f M₁ (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (h₂ : HasFDerivWithinAt f M₂ (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (hφ : HasFDerivWithinAt φ A s x) (hs : UniqueDiffWithinAt ℝ s x) :
    M₁.comp A.normalGraphL.range.subtypeL = M₂.comp A.normalGraphL.range.subtypeL := by
  have heq := h₁.comp_normalGraphL_eq hφ
    (h₂.comp x hφ.normalGraphEmbedding (mapsTo_image _ _)) hs
  ext v
  obtain ⟨w, hw⟩ := v.property
  have hw' : A.normalGraphL w = (v : WithLp 2 (ℝ × E)) := hw
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, hw'] using
    congrArg (fun D : E →L[ℝ] F => D w) heq

/-- The tangential derivative in graph coordinates is the pullback derivative composed
with the second projection and restricted to the tangent plane. -/
theorem comp_subtypeL_normalGraphL_range_eq_of_comp_normalGraphEmbedding
    (hM : HasFDerivWithinAt f M (TauCeti.normalGraphEmbedding φ '' s)
      (TauCeti.normalGraphEmbedding φ x))
    (hφ : HasFDerivWithinAt φ A s x)
    (hB : HasFDerivWithinAt (f ∘ TauCeti.normalGraphEmbedding φ) B s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    M.comp A.normalGraphL.range.subtypeL =
      (B.comp (WithLp.sndL 2 ℝ ℝ E)).comp A.normalGraphL.range.subtypeL :=
  hM.comp_subtypeL_normalGraphL_range_eq hB.of_comp_normalGraphEmbedding hφ hs

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
  constructor
  · intro hf
    exact hf.comp x hφ.hasFDerivWithinAt.normalGraphEmbedding.differentiableWithinAt
      (mapsTo_image _ _)
  · intro hf
    exact hf.hasFDerivWithinAt.of_comp_normalGraphEmbedding.differentiableWithinAt

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
  obtain ⟨M, hM⟩ := hf
  refine ⟨M.comp A.normalGraphL.range.subtypeL, ⟨M, hM, rfl⟩, ?_⟩
  rintro D ⟨N, hN, rfl⟩
  exact hN.comp_subtypeL_normalGraphL_range_eq hM hφ hs

end DifferentiableWithinAt

namespace HasFDerivAt

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {B : E →L[ℝ] F} {x : E}

/-- A derivative of the pullback gives a within-derivative on the full graph.
No differentiability of the graphing function is required. -/
theorem of_comp_normalGraphEmbedding
    (h : HasFDerivAt (f ∘ TauCeti.normalGraphEmbedding φ) B x) :
    HasFDerivWithinAt f (B.comp (WithLp.sndL 2 ℝ ℝ E))
      (range (TauCeti.normalGraphEmbedding φ)) (TauCeti.normalGraphEmbedding φ x) := by
  simpa only [image_univ] using
    h.hasFDerivWithinAt.of_comp_normalGraphEmbedding (s := univ)

end HasFDerivAt
