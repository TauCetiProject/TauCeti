/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Defs

import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Range

/-!
# Differentiation on parametrized sets

A differentiable left inverse of a parametrization lifts pullback derivatives to its image.
Conversely, derivatives on the image agree on the range of the parametrization derivative
when derivatives on the parameter set are unique. These statements do not assume injectivity
of the derivative or finite-dimensionality, and apply in arbitrary codimension.
-/

public section

open Set

variable {𝕜 E G F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]
  {γ : E → G} {π : G → E} {f : G → F} {s : Set E} {x : E}
  {T : E →L[𝕜] G} {P : G →L[𝕜] E} {B : E →L[𝕜] F} {M M₁ M₂ : G →L[𝕜] F}

/-- A differentiable left inverse lifts a pullback within-derivative to the image.
No regularity of the parametrization itself is required. -/
theorem HasFDerivWithinAt.of_comp_right_of_leftInvOn
    (h : HasFDerivWithinAt (f ∘ γ) B s x)
    (hπ : HasFDerivWithinAt π P (γ '' s) (γ x))
    (hi : LeftInvOn π γ (insert x s)) :
    HasFDerivWithinAt f (B.comp P) (γ '' s) (γ x) := by
  have hx : π (γ x) = x := hi (mem_insert x s)
  have hm : MapsTo π (γ '' s) s := by
    rintro _ ⟨y, hy, rfl⟩
    simpa only [hi (mem_insert_of_mem x hy)] using hy
  have h' : HasFDerivWithinAt (f ∘ γ) B s (π (γ x)) := hx.symm ▸ h
  apply (h'.comp (γ x) hπ hm).congr
  · rintro _ ⟨y, hy, rfl⟩
    simp only [Function.comp_apply, hi (mem_insert_of_mem x hy)]
  · simp only [Function.comp_apply, hx]

/-- Two derivatives within a parametrized image agree on the range of the parametrization's
derivative if derivatives on the parameter set are unique at the base point. -/
theorem HasFDerivWithinAt.comp_subtypeL_range_eq [T2Space F]
    (h₁ : HasFDerivWithinAt f M₁ (γ '' s) (γ x))
    (h₂ : HasFDerivWithinAt f M₂ (γ '' s) (γ x))
    (hγ : HasFDerivWithinAt γ T s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    M₁.comp T.range.subtypeL = M₂.comp T.range.subtypeL := by
  apply (ContinuousLinearMap.comp_subtypeL_range_eq_iff T M₁ M₂).mpr
  exact hs.eq (h₁.comp x hγ (mapsTo_image _ _)) (h₂.comp x hγ (mapsTo_image _ _))

/-- Differentiability on a parametrized image gives a unique restriction of the derivative
to the derivative range, when the parametrization is differentiable and parameter derivatives
are unique. No inverse of the parametrization is needed. -/
theorem DifferentiableWithinAt.existsUnique_hasFDerivWithinAt_image_comp_subtypeL [T2Space F]
    (hf : DifferentiableWithinAt 𝕜 f (γ '' s) (γ x))
    (hγ : HasFDerivWithinAt γ T s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    ∃! D : T.range →L[𝕜] F, ∃ M : G →L[𝕜] F,
      HasFDerivWithinAt f M (γ '' s) (γ x) ∧ M.comp T.range.subtypeL = D := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨M.comp T.range.subtypeL, ⟨M, hM, rfl⟩, ?_⟩
  rintro D ⟨N, hN, rfl⟩
  exact hN.comp_subtypeL_range_eq hM hγ hs

/-- A differentiable parametrization with a differentiable left inverse preserves and
reflects within-differentiability on its image. -/
theorem DifferentiableWithinAt.image_iff_of_leftInvOn
    (hγ : DifferentiableWithinAt 𝕜 γ s x)
    (hπ : DifferentiableWithinAt 𝕜 π (γ '' s) (γ x))
    (hi : LeftInvOn π γ (insert x s)) :
    DifferentiableWithinAt 𝕜 f (γ '' s) (γ x) ↔
      DifferentiableWithinAt 𝕜 (f ∘ γ) s x := by
  constructor
  · intro hf
    exact hf.comp x hγ (mapsTo_image _ _)
  · intro hf
    exact (hf.hasFDerivWithinAt.of_comp_right_of_leftInvOn
      hπ.hasFDerivWithinAt hi).differentiableWithinAt

/-- The chosen image derivative pulls back to the chosen parameter derivative for a
differentiable parametrization with a differentiable left inverse, provided parameter derivatives
are unique.
The identity also holds when the function is not differentiable, as both sides then vanish. -/
theorem DifferentiableWithinAt.fderivWithin_image_comp_of_leftInvOn [T2Space F]
    (hγ : DifferentiableWithinAt 𝕜 γ s x)
    (hπ : DifferentiableWithinAt 𝕜 π (γ '' s) (γ x))
    (hi : LeftInvOn π γ (insert x s)) (hs : UniqueDiffWithinAt 𝕜 s x) :
    (fderivWithin 𝕜 f (γ '' s) (γ x)).comp (fderivWithin 𝕜 γ s x) =
      fderivWithin 𝕜 (f ∘ γ) s x := by
  by_cases hf : DifferentiableWithinAt 𝕜 f (γ '' s) (γ x)
  · exact ((hf.hasFDerivWithinAt.comp x hγ.hasFDerivWithinAt
      (mapsTo_image _ _)).fderivWithin hs).symm
  · rw [fderivWithin_zero_of_not_differentiableWithinAt hf,
      fderivWithin_zero_of_not_differentiableWithinAt
        (mt (hγ.image_iff_of_leftInvOn hπ hi).mpr hf)]
    simp
