/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Restricting the scalars of manifold derivatives

Let `𝕜'` be a normed algebra over `𝕜`, and let `E` and `E'` be normed spaces over both fields,
compatibly. A manifold charted by `E` carries the trivial models `𝓘(𝕜', E)` and `𝓘(𝕜, E)` with the
same charts. This file shows that a map between such manifolds which is differentiable for the
models over `𝕜'` is differentiable for the models over `𝕜`, and that its derivative over `𝕜` is the
derivative over `𝕜'` with scalars restricted to `𝕜`.

The tangent spaces `TangentSpace 𝓘(𝕜', E) x` and `TangentSpace 𝓘(𝕜, E) x` are both the model space
`E`, but they are distinct types carrying module structures over different fields. The comparison of
derivatives is therefore stated after reading both derivatives in the model spaces through the
identifications `tangentSpaceCastModel`, which is also how `HasMFDerivWithinAt` reads a derivative
in charts.

The main example is a holomorphic map between complex manifolds modelled on `𝓘(ℂ, E)` and
`𝓘(ℂ, E')`: its real derivative is its complex derivative regarded as an `ℝ`-linear map.

## Main results

* `MDifferentiableWithinAt.restrictScalars`, `MDifferentiableAt.restrictScalars`,
  `MDifferentiableOn.restrictScalars`, `MDifferentiable.restrictScalars`: differentiability over
  `𝕜'` implies differentiability over `𝕜`.
* `HasMFDerivWithinAt.restrictScalars`, `HasMFDerivAt.restrictScalars`: a derivative over `𝕜'`,
  with scalars restricted to `𝕜`, is a derivative over `𝕜`.
* `MDifferentiableWithinAt.restrictScalars_mfderivWithin`,
  `MDifferentiableAt.mfderiv_restrictScalars`: the derivative over `𝕜` is the derivative over `𝕜'`
  with scalars restricted to `𝕜`.
-/

public section

open Set
open scoped Manifold

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜' E'] [IsScalarTower 𝕜 𝕜' E'] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {N : Type*} [TopologicalSpace N] [ChartedSpace E' N]
  {f : M → N} {s : Set M} {x : M}

variable (𝕜)

/-- A map which is differentiable within a set at a point for the models over `𝕜'` is
differentiable within that set at that point for the models over the smaller field `𝕜`. -/
theorem MDifferentiableWithinAt.restrictScalars
    (h : MDifferentiableWithinAt 𝓘(𝕜', E) 𝓘(𝕜', E') f s x) :
    MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x := by
  simp only [mdifferentiableWithinAt_iff, mfld_simps] at h ⊢
  exact ⟨h.1, h.2.restrictScalars 𝕜⟩

/-- A map which is differentiable at a point for the models over `𝕜'` is differentiable at that
point for the models over the smaller field `𝕜`. -/
theorem MDifferentiableAt.restrictScalars (h : MDifferentiableAt 𝓘(𝕜', E) 𝓘(𝕜', E') f x) :
    MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
  mdifferentiableWithinAt_univ.mp (h.mdifferentiableWithinAt.restrictScalars 𝕜)

/-- A map which is differentiable on a set for the models over `𝕜'` is differentiable on that set
for the models over the smaller field `𝕜`. -/
theorem MDifferentiableOn.restrictScalars (h : MDifferentiableOn 𝓘(𝕜', E) 𝓘(𝕜', E') f s) :
    MDifferentiableOn 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
  fun x hx ↦ (h x hx).restrictScalars 𝕜

/-- A map which is differentiable for the models over `𝕜'` is differentiable for the models over
the smaller field `𝕜`. -/
theorem MDifferentiable.restrictScalars (h : MDifferentiable 𝓘(𝕜', E) 𝓘(𝕜', E') f) :
    MDifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
  fun x ↦ (h x).restrictScalars 𝕜

/-- If `f'` is a derivative of `f` within a set at a point for the models over `𝕜'`, and `g'` is a
`𝕜`-linear map between the tangent spaces over `𝕜` which agrees with `f'` once both are read in the
model spaces, then `g'` is a derivative of `f` within that set at that point for the models over
`𝕜`. -/
theorem HasMFDerivWithinAt.restrictScalars
    {f' : TangentSpace 𝓘(𝕜', E) x →L[𝕜'] TangentSpace 𝓘(𝕜', E') (f x)}
    {g' : TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)}
    (h : HasMFDerivWithinAt 𝓘(𝕜', E) 𝓘(𝕜', E') f s x f')
    (hg : ((tangentSpaceCastModel 𝓘(𝕜', E') (f x) : _ →L[𝕜'] E') ∘L f' ∘L
        ((tangentSpaceCastModel 𝓘(𝕜', E) x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 =
      (tangentSpaceCastModel 𝓘(𝕜, E') (f x) : _ →L[𝕜] E') ∘L g' ∘L
        ((tangentSpaceCastModel 𝓘(𝕜, E) x).symm : E →L[𝕜] _)) :
    HasMFDerivWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') f s x g' := by
  have hf := h.2.restrictScalars 𝕜
  simp only [hg, mfld_simps] at hf
  simp only [HasMFDerivWithinAt, mfld_simps]
  exact ⟨h.1, hf⟩

/-- If `f'` is a derivative of `f` at a point for the models over `𝕜'`, and `g'` is a `𝕜`-linear map
between the tangent spaces over `𝕜` which agrees with `f'` once both are read in the model spaces,
then `g'` is a derivative of `f` at that point for the models over `𝕜`. -/
theorem HasMFDerivAt.restrictScalars
    {f' : TangentSpace 𝓘(𝕜', E) x →L[𝕜'] TangentSpace 𝓘(𝕜', E') (f x)}
    {g' : TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E') (f x)}
    (h : HasMFDerivAt 𝓘(𝕜', E) 𝓘(𝕜', E') f x f')
    (hg : ((tangentSpaceCastModel 𝓘(𝕜', E') (f x) : _ →L[𝕜'] E') ∘L f' ∘L
        ((tangentSpaceCastModel 𝓘(𝕜', E) x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 =
      (tangentSpaceCastModel 𝓘(𝕜, E') (f x) : _ →L[𝕜] E') ∘L g' ∘L
        ((tangentSpaceCastModel 𝓘(𝕜, E) x).symm : E →L[𝕜] _)) :
    HasMFDerivAt 𝓘(𝕜, E) 𝓘(𝕜, E') f x g' :=
  hasMFDerivWithinAt_univ.mp (h.hasMFDerivWithinAt.restrictScalars 𝕜 hg)

/-- At a point where `f` is differentiable within a set for the models over `𝕜'`, and where the set
has unique derivatives over the smaller field `𝕜`, the derivative of `f` within the set over `𝕜` is
its derivative over `𝕜'` with scalars restricted to `𝕜`, both read in the model spaces. -/
theorem MDifferentiableWithinAt.restrictScalars_mfderivWithin
    (h : MDifferentiableWithinAt 𝓘(𝕜', E) 𝓘(𝕜', E') f s x)
    (hs : UniqueMDiffWithinAt 𝓘(𝕜, E) s x) :
    ((tangentSpaceCastModel 𝓘(𝕜', E') (f x) : _ →L[𝕜'] E') ∘L
        mfderivWithin 𝓘(𝕜', E) 𝓘(𝕜', E') f s x ∘L
        ((tangentSpaceCastModel 𝓘(𝕜', E) x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 =
      (tangentSpaceCastModel 𝓘(𝕜, E') (f x) : _ →L[𝕜] E') ∘L
        mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f s x ∘L
        ((tangentSpaceCastModel 𝓘(𝕜, E) x).symm : E →L[𝕜] _) := by
  have h₁ := h.hasMFDerivWithinAt.2.restrictScalars 𝕜
  have h₂ := (h.restrictScalars 𝕜).hasMFDerivWithinAt.2
  simp only [UniqueMDiffWithinAt, mfld_simps] at h₁ h₂ hs
  exact hs.eq h₁ h₂

/-- At a point where `f` is differentiable for the models over `𝕜'`, the derivative of `f` over the
smaller field `𝕜` is its derivative over `𝕜'` with scalars restricted to `𝕜`, both read in the model
spaces. For instance, the real derivative of a holomorphic map is its complex derivative. -/
theorem MDifferentiableAt.mfderiv_restrictScalars
    (h : MDifferentiableAt 𝓘(𝕜', E) 𝓘(𝕜', E') f x) :
    (tangentSpaceCastModel 𝓘(𝕜, E') (f x) : _ →L[𝕜] E') ∘L
        mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x ∘L
        ((tangentSpaceCastModel 𝓘(𝕜, E) x).symm : E →L[𝕜] _) =
      ((tangentSpaceCastModel 𝓘(𝕜', E') (f x) : _ →L[𝕜'] E') ∘L
        mfderiv 𝓘(𝕜', E) 𝓘(𝕜', E') f x ∘L
        ((tangentSpaceCastModel 𝓘(𝕜', E) x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 := by
  simpa only [mfderivWithin_univ] using
    (h.mdifferentiableWithinAt.restrictScalars_mfderivWithin 𝕜 (uniqueMDiffWithinAt_univ _)).symm
