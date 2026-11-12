/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.TangentCone.Graph
import Mathlib.Analysis.Calculus.FDeriv.Comp

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
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {B : E →L[ℝ] F} {s : Set E} {x : E}

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

end HasFDerivWithinAt

namespace DifferentiableWithinAt

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {s : Set E} {x : E}

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

end DifferentiableWithinAt

namespace HasFDerivAt

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {φ : E → ℝ} {f : WithLp 2 (ℝ × E) → F} {A : E →L[ℝ] ℝ} {B : E →L[ℝ] F} {x : E}

/-- A differentiable pullback on a differentiable graph determines a unique derivative on
the tangent plane. The ambient within-derivative used to represent it is not unique. -/
theorem existsUnique_restrict_normalGraph
    (h : HasFDerivAt (f ∘ TauCeti.normalGraphEmbedding φ) B x)
    (hφ : HasFDerivAt φ A x) :
    ∃! D : A.normalGraphL.range →L[ℝ] F,
      ∃ L : WithLp 2 (ℝ × E) →L[ℝ] F,
        HasFDerivWithinAt f L (range (TauCeti.normalGraphEmbedding φ))
          (TauCeti.normalGraphEmbedding φ x) ∧
        L.comp A.normalGraphL.range.subtypeL = D := by
  have hL := h.hasFDerivWithinAt.of_comp_normalGraphEmbedding (s := univ)
  rw [image_univ] at hL
  let L := B.comp (WithLp.sndL 2 ℝ ℝ E)
  refine ⟨L.comp A.normalGraphL.range.subtypeL, ⟨L, hL, rfl⟩, ?_⟩
  rintro D ⟨M, hM, rfl⟩
  have heq := hM.unique_on hL
  have hcone := hφ.tangentConeAt_normalGraphEmbedding_image (s := univ) (by simp)
  rw [image_univ] at hcone
  rw [hcone] at heq
  ext v
  exact heq v.property

end HasFDerivAt
